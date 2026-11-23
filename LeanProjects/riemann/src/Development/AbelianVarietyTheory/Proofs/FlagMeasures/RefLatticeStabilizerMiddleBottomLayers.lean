import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIpowSmulOfSmulMem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapCompNegStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReferenceLatticeMemOfMemInnerSpanStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.RowStab

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem mem_one_smul {𝔡 : Ideal (𝓞 K)} {M : Submodule (𝓞 K) V} {y : V} (hy : y ∈ M) :
    y ∈ ipow 𝔡 0 • M := by
  have h1 : (1 : K) ∈ ipow 𝔡 0 := by rw [ipow_zero]; exact Submodule.one_le.mp le_rfl
  simpa using Submodule.smul_mem_smul h1 hy

theorem pair_mem {𝔡 : Ideal (𝓞 K)} (h𝔡 : 𝔡 ≠ ⊥) (h𝔡s : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K))
    {M : Submodule (𝓞 K) V} (hM : ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)) {m n : ℤ} {x y : V}
    (hx : x ∈ ipow 𝔡 m • M) (hy : y ∈ ipow 𝔡 n • M) : H.B x y ∈ ipow 𝔡 (m + n) := by
  apply mem_ipow_of_mul h𝔡
  intro t ht
  have h1 : t • x ∈ M := smul_mem_of_mem_ipow_smul h𝔡 hx ht
  rw [show t * H.B x y = H.B (t • x) y by simp]
  have := mem_ipow_of_mul h𝔡 (m := n) (n := 0) (x := H.B (t • x) y) ?_
  · simpa using this
  intro t' ht'
  rw [ipow_zero]
  have := hM _ h1 _ (smul_mem_of_mem_ipow_smul h𝔡 hy (star_mem_ipow h𝔡 h𝔡s _ ht'))
  simpa [mul_comm, mul_left_comm, starRingEnd_apply, star_star] using this

theorem lat_int {L : Submodule (𝓞 K) V} {S I : Submodule K V} (hL : IsUnimodMod H L S I) :
    ∀ x ∈ L, ∀ y ∈ L, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
  intro x hx y hy
  have : x ∈ dual H L := by rw [hL.2]; exact hx
  exact ((mem_dual_iff H L x).mp this).2 y hy

section NFl
variable (N : NF H r)

theorem e_mem_X (a : Fin r) : N.F.e a.castSucc ∈ N.F.X :=
  Submodule.subset_span ⟨a, a.isLt, rfl⟩

theorem e'_mem_X (a : Fin r) : N.F'.e a.castSucc ∈ N.F'.X :=
  Submodule.subset_span ⟨a, a.isLt, rfl⟩

theorem iso_X (F : FlagD H r) : ∀ x ∈ F.X, ∀ y ∈ F.X, H.B x y = 0 := by
  have h1 : ∀ a : Fin r, ∀ y ∈ F.X, H.B (F.e a.castSucc) y = 0 := by
    intro a y hy
    have : F.X ≤ LinearMap.ker (H.B (F.e a.castSucc)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, -, rfl⟩
      exact F.iso a b
    exact this hy
  intro x hx y hy
  have : F.X ≤ LinearMap.ker (H.B.flip y) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, -, rfl⟩
    exact h1 b y hy
  exact this hx

theorem c_ne : N.c ≠ 0 := by
  intro h; have := N.c_norm; simp [h] at this

theorem e'_eq (b : Fin r) (hb : N.j ≤ b.val) : N.F'.e b.castSucc = N.c • N.F.e b.castSucc :=
  N.same b.castSucc hb

theorem e_mem_II (b : Fin r) (hb : N.j ≤ b.val) : N.F.e b.castSucc ∈ II N.F N.F' := by
  refine ⟨e_mem_X N b, ?_⟩
  have h := e'_mem_X N b
  rw [e'_eq N b hb] at h
  have := N.F'.X.smul_mem (N.c)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ (c_ne N), one_smul] at this

theorem B_e'_e (a b : Fin r) (hb : N.j ≤ b.val) : H.B (N.F'.e a.castSucc) (N.F.e b.castSucc) = 0 := by
  have h := N.F'.iso a b
  rw [e'_eq N b hb, map_smulₛₗ] at h
  have hc : (starRingEnd K) N.c ≠ 0 := by simpa using c_ne N
  simpa [hc] using h

theorem B_e_e' (a b : Fin r) (hb : N.j ≤ b.val) : H.B (N.F.e b.castSucc) (N.F'.e a.castSucc) = 0 := by
  rw [← H.herm, B_e'_e N a b hb, star_zero]

theorem Wn_B_e {w : V} (hw : w ∈ N.Wn) (a : Fin r) : H.B w (N.F.e a.castSucc) = 0 :=
  (mem_perp_iff H _ w).mp hw _ (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X N a)))

theorem Wn_B_e' {w : V} (hw : w ∈ N.Wn) (a : Fin r) : H.B w (N.F'.e a.castSucc) = 0 :=
  (mem_perp_iff H _ w).mp hw _ (Submodule.mem_sup_left (Submodule.mem_sup_right (e'_mem_X N a)))

theorem Wn_B_ist {w : V} (hw : w ∈ N.Wn) (b : Fin r) (hb : N.j ≤ b.val) : H.B w (N.ist b) = 0 :=
  (mem_perp_iff H _ w).mp hw _ (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))

theorem B_ist_e (a b : Fin r) (hb : N.j ≤ b.val) :
    H.B (N.ist b) (N.F.e a.castSucc) = if a = b then 1 else 0 := by
  rw [← H.herm, N.ist_e a b hb]; split_ifs <;> simp

end NFl

end GlobalTheory.RowStab

namespace GlobalTheory.RowStab

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem mem_line {A : Submodule (𝓞 K) K} {v x : V} : x ∈ line A v ↔ ∃ t ∈ A, t • v = x := by
  simp [line]

theorem line_le {A : Submodule (𝓞 K) K} {v : V} {M : Submodule (𝓞 K) V} :
    line A v ≤ M ↔ ∀ t ∈ A, t • v ∈ M := by
  constructor
  · intro h t ht; exact h (mem_line.mpr ⟨t, ht, rfl⟩)
  · intro h x hx; obtain ⟨t, ht, rfl⟩ := mem_line.mp hx; exact h t ht

section NFr
variable (N : NF H r) (L : Submodule (𝓞 K) V)

theorem ref_e {a : Fin r} {t : K} (ht : t ∈ N.aa a) : t • N.F.e a.castSucc ∈ N.Ref L := by
  refine Submodule.mem_sup_left ?_
  refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
  exact Submodule.mem_iSup_of_mem a (mem_line.mpr ⟨t, ht, rfl⟩)

theorem ref_e' {a : Fin r} (ha : a.val < N.j) {t : K} (ht : t ∈ N.aa a) :
    t • N.F'.e a.castSucc ∈ N.Ref L := by
  refine Submodule.mem_sup_left ?_
  refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right ?_))
  exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha (mem_line.mpr ⟨t, ht, rfl⟩))

theorem ref_ist {b : Fin r} (hb : N.j ≤ b.val) {t : K} (ht : t ∈ ipow N.𝔡 ((r : ℤ) - b.val)) :
    t • N.ist b ∈ N.Ref L := by
  refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
  exact Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hb (mem_line.mpr ⟨t, ht, rfl⟩))

theorem ref_Wn {w : V} (hw : w ∈ L) (hw' : w ∈ N.Wn) : w ∈ N.Ref L :=
  Submodule.mem_sup_right ⟨hw, hw'⟩

theorem ref_coeff (a : Fin r) (ha : N.j ≤ a.val) : ∀ v ∈ N.Ref L, H.B v (N.ist a) ∈ N.aa a := by
  let Q : Submodule (𝓞 K) V := (N.aa a).comap ((H.B.flip (N.ist a)).restrictScalars (𝓞 K))
  have hQ : ∀ v, v ∈ Q ↔ H.B v (N.ist a) ∈ N.aa a := fun v => Iff.rfl
  suffices h : N.Ref L ≤ Q from fun v hv => (hQ v).mp (h hv)
  refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
  · refine iSup_le fun a' => line_le.mpr fun t ht => (hQ _).mpr ?_
    rw [map_smul, LinearMap.smul_apply, N.ist_e a' a ha, smul_eq_mul]
    split_ifs with h
    · subst h; simpa using ht
    · simp
  · refine iSup_le fun a' => iSup_le fun h' => line_le.mpr fun t ht => (hQ _).mpr ?_
    rw [map_smul, LinearMap.smul_apply, N.ist_e' a' a h' ha]; simp
  · refine line_le.mpr fun t ht => (hQ _).mpr ?_
    rw [map_smul, LinearMap.smul_apply, show H.B N.F.z (N.ist a) = 0 from N.normalForm_dual_orthogonal_last a ha]; simp
  · refine iSup_le fun a' => iSup_le fun h' => line_le.mpr fun t ht => (hQ _).mpr ?_
    rw [map_smul, LinearMap.smul_apply, N.ist_iso a' a h' ha]; simp
  · intro v hv
    exact (hQ _).mpr (by rw [Wn_B_ist N hv.2 a ha]; simp)

end NFr

end GlobalTheory.RowStab

namespace GlobalTheory.RowStab

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

def JJ (N : NF H r) : Finset (Fin r) := Finset.univ.filter (fun b => N.j ≤ b.val)

def eF (N : NF H r) : Fin r → V := fun a => N.F.e a.castSucc

theorem mem_JJ (N : NF H r) (b : Fin r) : b ∈ JJ N ↔ N.j ≤ b.val := by simp [JJ]

theorem gen_fix {ι : Type} (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) {v : V}
    (h1 : ∀ b ∈ J, H.B v (e b) = 0) (h2 : ∀ b ∈ J, H.B v (ρ b) = 0) : gen H J e ρ c v = v := by
  rw [gen_apply]
  conv_rhs => rw [← add_zero v]
  congr 1
  refine Finset.sum_eq_zero fun b hb => ?_
  simp [h1 b hb, h2 b hb]

theorem gen_perp {ι : Type} (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) {v : V}
    (h1 : ∀ b ∈ J, H.B v (e b) = 0) : gen H J e ρ c v = v - ∑ b ∈ J, H.B v (ρ b) • e b := by
  rw [gen_apply, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  simp [h1 b hb]

section NFg
variable (N : NF H r) (L : Submodule (𝓞 K) V)

theorem gen_ref (hz : N.F.z ∈ L) (hzW : N.F.z ∈ N.Wn) (hL : ∀ x ∈ L, ∀ y ∈ L, H.B x y ∈ (1 : Submodule (𝓞 K) K))
    (ρ : Fin r → V) (c : Fin r → Fin r → K) (hρW : ∀ b, ρ b ∈ N.Wn)
    (hρ : ∀ b : Fin r, N.j ≤ b.val → ρ b ∈ ipow N.𝔡 (-((r : ℤ) - b.val)) • (L ⊓ rs (𝓞 K) N.Wn))
    (hcI : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → c a b ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val))) :
    ∀ v ∈ N.Ref L, gen H (JJ N) (eF N) ρ c v ∈ N.Ref L := by
  set g := gen H (JJ N) (eF N) ρ c with hg
  have hM : ∀ x ∈ L ⊓ rs (𝓞 K) N.Wn, ∀ y ∈ L ⊓ rs (𝓞 K) N.Wn, H.B x y ∈ (1 : Submodule (𝓞 K) K) :=
    fun x hx y hy => hL x hx.1 y hy.1

  have hW : ∀ w ∈ L ⊓ rs (𝓞 K) N.Wn, g w ∈ N.Ref L := by
    intro w hw
    rw [hg, gen_perp (JJ N) (eF N) ρ c (fun b _ => Wn_B_e N hw.2 b)]
    refine sub_mem (ref_Wn N L hw.1 hw.2) (Submodule.sum_mem _ fun b hb => ?_)
    refine ref_e N L ?_
    have h1 := pair_mem N.𝔡_ne N.𝔡_star hM (hρ b ((mem_JJ N b).mp hb)) (mem_one_smul (𝔡 := N.𝔡) hw)
    rw [add_zero] at h1
    have h2 := star_mem_ipow N.𝔡_ne N.𝔡_star _ h1
    rwa [H.herm] at h2
  let Q : Submodule (𝓞 K) V := (N.Ref L).comap (g.restrictScalars (𝓞 K))
  have hQ : ∀ v, v ∈ Q ↔ g v ∈ N.Ref L := fun v => Iff.rfl
  suffices h : N.Ref L ≤ Q from fun v hv => (hQ v).mp (h hv)
  refine sup_le (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) ?_
  · refine iSup_le fun a => line_le.mpr fun t ht => (hQ _).mpr ?_
    rw [hg, gen_fix]
    · exact ref_e N L ht
    · intro b _; simp [eF, N.F.iso]
    · intro b _
      rw [map_smul, LinearMap.smul_apply, ← H.herm, Wn_B_e N (hρW b) a]; simp
  · refine iSup_le fun a => iSup_le fun ha => line_le.mpr fun t ht => (hQ _).mpr ?_
    rw [hg, gen_fix]
    · exact ref_e' N L ha ht
    · intro b hb; rw [map_smul, LinearMap.smul_apply]; simp [eF, B_e'_e N a b ((mem_JJ N b).mp hb)]
    · intro b _
      rw [map_smul, LinearMap.smul_apply, ← H.herm, Wn_B_e' N (hρW b) a]; simp
  · refine line_le.mpr fun t ht => (hQ _).mpr ?_
    obtain ⟨o, rfl⟩ := Submodule.mem_one.mp ht
    rw [algebraMap_smul, LinearMap.map_smul_of_tower]
    exact (N.Ref L).smul_mem o (hW _ ⟨hz, hzW⟩)
  · refine iSup_le fun a => iSup_le fun ha => line_le.mpr fun t ht => (hQ _).mpr ?_
    rw [hg, gen_apply]
    refine add_mem (ref_ist N L ha ht) (Submodule.sum_mem _ fun b hb => ?_)
    have hb' := (mem_JJ N b).mp hb
    have e1 : H.B (t • N.ist a) (eF N b) = if b = a then t else 0 := by
      rw [map_smul, LinearMap.smul_apply, eF, B_ist_e N b a ha]; split_ifs <;> simp
    have e2 : H.B (t • N.ist a) (ρ b) = 0 := by
      rw [map_smul, LinearMap.smul_apply, ← H.herm, Wn_B_ist N (hρW b) a ha]; simp
    rw [e1, e2, zero_smul, sub_zero]
    split_ifs with hba
    · subst hba
      refine add_mem ?_ (Submodule.sum_mem _ fun a' ha' => ref_e N L ?_)
      · have : t ∈ ipow N.𝔡 (-(-((r : ℤ) - b.val))) := by rwa [neg_neg]
        have := smul_mem_of_mem_ipow_smul N.𝔡_ne (hρ b hb') this
        exact ref_Wn N L this.1 this.2
      · have := ipow_mul_mem N.𝔡_ne (hcI a' b ((mem_JJ N a').mp ha') hb') ht
        unfold NF.aa; convert this using 2; ring
    · simp
  · intro w hw
    exact (hQ _).mpr (hW w hw)

end NFg

end GlobalTheory.RowStab

namespace GlobalTheory.RowStab

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem exists_stab (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) (L : Submodule (𝓞 K) V) (hz : N.F.z ∈ L)
    (hzW : N.F.z ∈ N.Wn) (hL : ∀ x ∈ L, ∀ y ∈ L, H.B x y ∈ (1 : Submodule (𝓞 K) K))
    (ρ : Fin r → V) (c : Fin r → Fin r → K) (hρW : ∀ b, ρ b ∈ N.Wn)
    (hρ : ∀ b : Fin r, N.j ≤ b.val → ρ b ∈ ipow N.𝔡 (-((r : ℤ) - b.val)) • (L ⊓ rs (𝓞 K) N.Wn))
    (hcI : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → c a b ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)))
    (hc : ∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) :
    ∃ s ∈ N.Gam (N.Ref L), ∀ v, s v = gen H (JJ N) (eF N) ρ c v := by
  set c' : Fin r → Fin r → K := fun a b => -c a b - H.B (ρ b) (ρ a) with hc'
  have hee : ∀ a b, H.B (eF N a) (eF N b) = 0 := N.F.iso
  have hρe : ∀ a b, H.B (ρ a) (eF N b) = 0 := fun a b => Wn_B_e N (hρW a) b
  have hρe' : ∀ a b, H.B ((-ρ) a) (eF N b) = 0 := fun a b => by simp [hρe]
  have comp1 : ∀ v, gen H (JJ N) (eF N) ρ c (gen H (JJ N) (eF N) (-ρ) c' v) = v :=
    GlobalTheory.T.hermitianUnipotentGeneratorMap_comp_neg H (JJ N) (eF N) ρ c c' hee hρe (fun a b => by simp only [hc']; ring)
  have comp2 : ∀ v, gen H (JJ N) (eF N) (-ρ) c' (gen H (JJ N) (eF N) ρ c v) = v := by
    have := GlobalTheory.T.hermitianUnipotentGeneratorMap_comp_neg H (JJ N) (eF N) (-ρ) c' c hee hρe' (fun a b => by
      simp only [hc', Pi.neg_apply, map_neg, LinearMap.neg_apply, neg_neg]; ring)
    simpa [neg_neg] using this
  set g := gen H (JJ N) (eF N) ρ c with hg
  let s : V ≃ₗ[K] V := LinearEquiv.ofLinear g (gen H (JJ N) (eF N) (-ρ) c')
    (LinearMap.ext comp1) (LinearMap.ext comp2)
  have hs : ∀ v, s v = g v := fun v => rfl
  have hM : ∀ x ∈ L ⊓ rs (𝓞 K) N.Wn, ∀ y ∈ L ⊓ rs (𝓞 K) N.Wn, H.B x y ∈ (1 : Submodule (𝓞 K) K) :=
    fun x hx y hy => hL x hx.1 y hy.1
  have hisom : ∀ u v, H.B (g u) (g v) = H.B u v := GlobalTheory.T.hermitianUnipotentGeneratorMap_isometry H (JJ N) (eF N) ρ c hee hρe hc
  have hbij : Function.Bijective (s : V →ₗ[K] V) := s.bijective
  have cus := GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N
  refine ⟨s, Subgroup.mem_inf.mpr ⟨(cus.1 s).mpr ⟨⟨hisom, hbij, ?_, ?_⟩, ⟨hisom, hbij, ?_, ?_⟩⟩, ?_⟩, hs⟩
  · intro a
    show g (N.F.e a.castSucc) - N.F.e a.castSucc ∈ _
    rw [hg, gen_fix (JJ N) (eF N) ρ c (fun b _ => N.F.iso a b)
      (fun b _ => by rw [← H.herm, show H.B (ρ b) (N.F.e a.castSucc) = 0 from hρe b a, star_zero]), sub_self]
    exact zero_mem _
  · intro y hy
    show g y - y ∈ _
    rw [hg, gen_perp (JJ N) (eF N) ρ c (fun b _ => by rw [← H.herm, eF, hy b, star_zero]), sub_sub_cancel_left]
    exact neg_mem (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (e_mem_X N b))
  · intro a
    show g (N.F'.e a.castSucc) - N.F'.e a.castSucc ∈ _
    rw [hg, gen_fix (JJ N) (eF N) ρ c (fun b hb => B_e'_e N a b ((mem_JJ N b).mp hb))
      (fun b _ => by rw [← H.herm, Wn_B_e' N (hρW b) a, star_zero]), sub_self]
    exact zero_mem _
  · intro y hy
    show g y - y ∈ _
    have h1 : ∀ b ∈ JJ N, H.B y (eF N b) = 0 := by
      intro b hb
      have h := hy b
      rw [e'_eq N b ((mem_JJ N b).mp hb), map_smul, LinearMap.smul_apply, smul_eq_mul] at h
      rw [← H.herm, eF, (mul_eq_zero.mp h).resolve_left (c_ne N), star_zero]
    rw [hg, gen_perp (JJ N) (eF N) ρ c h1, sub_sub_cancel_left]
    exact neg_mem (Submodule.sum_mem _ fun b hb =>
      Submodule.smul_mem _ _ (e_mem_II N b ((mem_JJ N b).mp hb)).2)
  · rw [MulAction.mem_stabilizer_iff]
    show (N.Ref L).map ((s : V →ₗ[K] V).restrictScalars (𝓞 K)) = N.Ref L
    have href := gen_ref N L hz hzW hL ρ c hρW hρ hcI
    have href' := gen_ref N L hz hzW hL (-ρ) c' (fun b => neg_mem (hρW b))
      (fun b hb => by rw [Pi.neg_apply]; exact neg_mem (hρ b hb)) (by
        intro a b ha hb
        have h1 : H.B (ρ b) (ρ a) ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) := by
          have := pair_mem N.𝔡_ne N.𝔡_star hM (hρ b hb) (hρ a ha)
          rwa [show -((r : ℤ) - b.val) + -((r : ℤ) - a.val) = -((r : ℤ) - a.val) - ((r : ℤ) - b.val) by ring]
            at this
        show -c a b - H.B (ρ b) (ρ a) ∈ _
        exact sub_mem (neg_mem (hcI a b ha hb)) h1)
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro v hv; exact href v hv
    · intro v hv
      exact Submodule.mem_map.mpr ⟨_, href' v hv, comp1 v⟩

end GlobalTheory.RowStab

namespace GlobalTheory.RowStab

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem gen_ist (N : NF H r) (ρ : Fin r → V) (c : Fin r → Fin r → K) (hρW : ∀ b, ρ b ∈ N.Wn)
    (b : Fin r) (hb : N.j ≤ b.val) :
    gen H (JJ N) (eF N) ρ c (N.ist b) = N.ist b + (ρ b + ∑ a ∈ JJ N, c a b • N.F.e a.castSucc) := by
  rw [gen_apply]
  congr 1
  rw [Finset.sum_congr rfl (g := fun b' => if b' = b then ρ b + ∑ a ∈ JJ N, c a b • N.F.e a.castSucc else 0)]
  · rw [Finset.sum_ite_eq']; simp [(mem_JJ N b).mpr hb]
  · intro b' _
    have e1 : H.B (N.ist b) (eF N b') = if b' = b then 1 else 0 := B_ist_e N b' b hb
    have e2 : H.B (N.ist b) (ρ b') = 0 := by rw [← H.herm, Wn_B_ist N (hρW b') b hb, star_zero]
    rw [e1, e2]
    split_ifs with h
    · subst h; simp [eF]
    · simp

theorem smul_le_Wn (N : NF H r) (L : Submodule (𝓞 K) V) (m : ℤ) {v : V}
    (hv : v ∈ ipow N.𝔡 m • (L ⊓ rs (𝓞 K) N.Wn)) : v ∈ N.Wn := by
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro t _ n hn; exact N.Wn.smul_mem t hn.2
  · intro x y hx hy; exact N.Wn.add_mem hx hy

end GlobalTheory.RowStab

open GlobalTheory.RowStab in

theorem GlobalTheory.RowStab.middle_bottom_layers : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r), ∀ L : Submodule (𝓞 K) V, IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → N.F.z ∈ L → (∀ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) → ∀ b : Fin r, N.j ≤ b.val → ∃ ρ ∈ ipow N.𝔡 (-((r : ℤ) - b.val)) • (L ⊓ rs (𝓞 K) N.Wn), s (N.ist b) - N.ist b - ρ ∈ II N.F N.F') ∧ (∀ ρ : Fin r → V, (∀ b : Fin r, ρ b ∈ ipow N.𝔡 (-((r : ℤ) - b.val)) • (L ⊓ rs (𝓞 K) N.Wn)) → ∃ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ ∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b - ρ b ∈ II N.F N.F') ∧ (∀ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') → ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val → H.B (s (N.ist b)) (N.ist a) ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) ∧ H.B (s (N.ist b)) (N.ist a) + star (H.B (s (N.ist a)) (N.ist b)) = 0) ∧ ∀ S : Fin r → Fin r → K, (∀ a b, S a b ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) ∧ S a b + star (S b a) = 0) → ∃ s ∈ N.Gam (N.Ref L), (∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ ∀ b : Fin r, N.j ≤ b.val → s (N.ist b) = N.ist b + ∑ a : Fin r, (if N.j ≤ a.val then S a b else 0) • N.F.e a.castSucc := by
  intro K V _ _ _ _ _ _ _ _ H hK r N L hLu hz
  have geo := GlobalTheory.DegCnt.NF.geometry K V H hK r N
  have cus := GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N
  have hzW : N.F.z ∈ N.Wn := by
    rw [geo.2.2.2.2.1]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hL := lat_int hLu
  have hisomR : ∀ s ∈ N.R, ∀ x y, H.B (s x) (s y) = H.B x y := fun s hs => ((cus.1 s).mp hs).1.1
  have hmap : ∀ s ∈ N.Gam (N.Ref L), ∀ v ∈ N.Ref L, s v ∈ N.Ref L := by
    intro s hs v hv
    have h2 : s • N.Ref L = N.Ref L := (Subgroup.mem_inf.mp hs).2
    rw [← h2]
    exact Submodule.mem_map_of_mem (f := (s : V →ₗ[K] V).restrictScalars (𝓞 K)) hv
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro s hs hfix b hb
    have hsR : s ∈ N.R := (Subgroup.mem_inf.mp hs).1
    set d := s (N.ist b) - N.ist b with hd
    set ρ := d - ∑ a ∈ JJ N, H.B d (N.ist a) • N.F.e a.castSucc with hρdef
    have hdX : ∀ a : Fin r, H.B d (N.F.e a.castSucc) = 0 := by
      intro a
      have := hisomR s hsR (N.ist b) (N.F.e a.castSucc)
      rw [hfix a] at this
      rw [hd, map_sub, LinearMap.sub_apply, this, sub_self]
    have hdX' : ∀ a : Fin r, a.val < N.j → H.B d (N.F'.e a.castSucc) = 0 := by
      intro a ha
      have hs' : s⁻¹ ∈ N.R := inv_mem hsR
      have hin : s⁻¹ (N.F'.e a.castSucc) - N.F'.e a.castSucc ∈ N.F'.Xa a.val := ((cus.1 s⁻¹).mp hs').2.2.2.1 a
      have hker : N.F'.Xa a.val ≤ LinearMap.ker (H.B (N.ist b)) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨a', ha', rfl⟩
        show H.B (N.ist b) (N.F'.e a'.castSucc) = 0
        rw [← H.herm, N.ist_e' a' b (lt_trans ha' ha) hb, star_zero]
      have e1 : H.B (s (N.ist b)) (N.F'.e a.castSucc) = H.B (N.ist b) (s⁻¹ (N.F'.e a.castSucc)) := by
        have := hisomR s hsR (N.ist b) (s⁻¹ (N.F'.e a.castSucc))
        rw [← this]
        congr 1
        show N.F'.e a.castSucc = (s * s⁻¹) (N.F'.e a.castSucc)
        rw [mul_inv_cancel]; rfl
      have h0 : H.B (N.ist b) (s⁻¹ (N.F'.e a.castSucc) - N.F'.e a.castSucc) = 0 := hker hin
      rw [map_sub] at h0
      rw [hd, map_sub, LinearMap.sub_apply, e1, sub_eq_zero.mp h0, sub_self]
    have hρX : ∀ a : Fin r, H.B ρ (N.F.e a.castSucc) = 0 := by
      intro a
      rw [hρdef, map_sub, LinearMap.sub_apply, hdX a, map_sum, LinearMap.sum_apply]
      simp [N.F.iso]
    have hρW : ρ ∈ N.Wn := by
      show ρ ∈ perp H _
      rw [mem_perp_iff]
      intro x hx
      suffices h : N.F.X ⊔ N.F'.X ⊔ N.Ist ≤ LinearMap.ker (H.B ρ) from h hx
      refine sup_le (sup_le ?_ ?_) ?_
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨a, -, rfl⟩
        exact hρX a
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨a, -, rfl⟩
        show H.B ρ (N.F'.e a.castSucc) = 0
        by_cases ha : N.j ≤ a.val
        · rw [e'_eq N a ha, map_smulₛₗ, hρX a, smul_zero]
        · rw [hρdef, map_sub, LinearMap.sub_apply, hdX' a (lt_of_not_ge ha), map_sum, LinearMap.sum_apply]
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
          rw [Finset.sum_eq_zero fun a' ha' => by rw [B_e_e' N a a' ((mem_JJ N a').mp ha'), mul_zero], sub_zero]
      · refine Submodule.span_le.mpr ?_
        rintro _ ⟨a, ha, rfl⟩
        show H.B ρ (N.ist a) = 0
        rw [hρdef, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply]
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        rw [Finset.sum_congr rfl (g := fun a' => if a' = a then H.B d (N.ist a) else 0)]
        · rw [Finset.sum_ite_eq']; simp [(mem_JJ N a).mpr ha]
        · intro a' _
          rw [N.ist_e a' a ha]; split_ifs with h <;> simp [h]
    refine ⟨ρ, ?_, ?_⟩
    · apply mem_ipow_smul_of_smul_mem N.𝔡_ne
      intro t ht
      rw [neg_neg] at ht
      have h1 : t • N.ist b ∈ N.Ref L := ref_ist N L hb ht
      have h2 : t • d ∈ N.Ref L := by
        rw [hd, smul_sub, ← LinearEquiv.map_smul]
        exact sub_mem (hmap s hs _ h1) h1
      have h3 : t • ρ ∈ N.Ref L := by
        rw [hρdef, smul_sub, Finset.smul_sum]
        refine sub_mem h2 (Submodule.sum_mem _ fun a ha => ?_)
        rw [smul_smul]
        refine ref_e N L ?_
        have := ref_coeff N L a ((mem_JJ N a).mp ha) _ h2
        rwa [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      have h4 : t • ρ ∈ N.Wn := N.Wn.smul_mem t hρW
      exact ⟨GlobalTheory.T.referenceLattice_mem_of_mem_innerSpan K V H hK r N L hz _ h3 h4, h4⟩
    · show d - ρ ∈ _
      rw [hρdef, sub_sub_cancel]
      exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (e_mem_II N a ((mem_JJ N a).mp ha))
  ·
    intro ρ hρ
    obtain ⟨w0, hw0⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram K hK
    have hρW : ∀ b, ρ b ∈ N.Wn := fun b => smul_le_Wn N L _ (hρ b)
    have hM : ∀ x ∈ L ⊓ rs (𝓞 K) N.Wn, ∀ y ∈ L ⊓ rs (𝓞 K) N.Wn, H.B x y ∈ (1 : Submodule (𝓞 K) K) :=
      fun x hx y hy => hL x hx.1 y hy.1
    let c : Fin r → Fin r → K := fun a b =>
      if a < b then -H.B (ρ b) (ρ a) else if a = b then -((w0 : K) * H.B (ρ a) (ρ a)) else 0
    have hrel : ∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0 := by
      intro a b
      rcases lt_trichotomy a b with h | h | h
      · simp only [c, if_pos h, if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h), star_neg, H.herm]; ring
      · subst h
        simp only [c, lt_irrefl, if_false, if_true, star_neg, star_mul', H.herm]
        linear_combination (-(H.B (ρ a) (ρ a))) * hw0
      · simp only [c, if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h), if_pos h, star_zero]; ring
    have hcI : ∀ a b : Fin r, N.j ≤ a.val → N.j ≤ b.val →
        c a b ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) := by
      intro a b ha hb
      have h1 : ∀ a b : Fin r, H.B (ρ b) (ρ a) ∈ ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - b.val)) := by
        intro a b
        have := pair_mem N.𝔡_ne N.𝔡_star hM (hρ b) (hρ a)
        rwa [show -((r : ℤ) - b.val) + -((r : ℤ) - a.val) = -((r : ℤ) - a.val) - ((r : ℤ) - b.val) by ring]
          at this
      simp only [c]
      split_ifs with h h'
      · exact neg_mem (h1 a b)
      · subst h'
        refine neg_mem ?_
        have h2 := Submodule.smul_mem (ipow N.𝔡 (-((r : ℤ) - a.val) - ((r : ℤ) - a.val))) w0 (h1 a a)
        rw [Algebra.smul_def] at h2
        exact h2
      · exact zero_mem _
    obtain ⟨s, hs, hsv⟩ := exists_stab hK N L hz hzW hL ρ c hρW (fun b _ => hρ b) hcI hrel
    refine ⟨s, hs, fun a => ?_, fun b hb => ?_⟩
    · rw [hsv, gen_fix (JJ N) (eF N) ρ c (fun b _ => N.F.iso a b)
        (fun b _ => by rw [← H.herm, Wn_B_e N (hρW b) a, star_zero])]
    · rw [hsv, gen_ist N ρ c hρW b hb, add_sub_cancel_left, add_sub_cancel_left]
      exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (e_mem_II N a ((mem_JJ N a).mp ha))
  ·
    intro s hs _ hI a b ha hb
    have hsR : s ∈ N.R := (Subgroup.mem_inf.mp hs).1
    constructor
    · have := mem_ipow_of_mul N.𝔡_ne (m := -((r : ℤ) - b.val)) (n := -((r : ℤ) - a.val))
        (x := H.B (s (N.ist b)) (N.ist a)) (fun t ht => by
          rw [neg_neg] at ht
          have h1 := ref_coeff N L a ha _ (hmap s hs _ (ref_ist N L hb ht))
          rwa [LinearEquiv.map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1)
      rwa [show -((r : ℤ) - b.val) + -((r : ℤ) - a.val) = -((r : ℤ) - a.val) - ((r : ℤ) - b.val) by ring]
        at this
    · have hiso := hisomR s hsR (N.ist b) (N.ist a)
      have hX := iso_X N.F _ (hI b hb).1 _ (hI a ha).1
      have e1 : s (N.ist b) = N.ist b + (s (N.ist b) - N.ist b) := by abel
      have e2 : s (N.ist a) = N.ist a + (s (N.ist a) - N.ist a) := by abel
      set ib := s (N.ist b) - N.ist b
      set ia := s (N.ist a) - N.ist a
      rw [e1, e2] at hiso ⊢
      simp only [map_add, LinearMap.add_apply, star_add, H.herm] at hiso ⊢
      simp only [N.ist_iso b a hb ha, N.ist_iso a b ha hb, hX, zero_add, add_zero] at hiso ⊢
      linear_combination hiso
  ·
    intro S hS
    have hrel : ∀ a b, star (S a b) + S b a + H.B ((0 : Fin r → V) a) ((0 : Fin r → V) b) = 0 := by
      intro a b
      have := (hS b a).2
      simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply, add_zero]
      rw [add_comm]; exact this
    obtain ⟨s, hs, hsv⟩ := exists_stab hK N L hz hzW hL 0 S (fun _ => zero_mem _) (fun _ _ => zero_mem _)
      (fun a b _ _ => (hS a b).1) hrel
    refine ⟨s, hs, fun a => ?_, fun b hb => ?_⟩
    · rw [hsv, gen_fix (JJ N) (eF N) 0 S (fun b _ => N.F.iso a b) (fun b _ => by simp)]
    · rw [hsv, gen_ist N 0 S (fun _ => zero_mem _) b hb, Pi.zero_apply, zero_add, JJ, Finset.sum_filter]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
