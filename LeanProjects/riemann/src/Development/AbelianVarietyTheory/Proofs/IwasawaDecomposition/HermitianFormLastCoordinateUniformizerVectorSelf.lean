import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMCastSuccLast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteOrbitsOfFiniteFibres
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TilX

section GenP

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_one_tmul_eq_zero (P : HeightOneSpectrum (𝓞 E)) (a : FiniteAdeleRing (𝓞 F) F) (h : a (P.under (𝓞 F)) = 0) :
    adAt F P ((1 : E) ⊗ₜ[F] a) = 0 := by
  have hs := (GlobalTheory.AdeleBaseChange.exists_finiteAdele_baseChange_equiv F E).choose_spec.2.2.2 a 0 P
  have h1 : ∀ n : ℕ, Valued.v (afIso F E ((1 : E) ⊗ₜ[F] a) P) ≤ WithZero.exp (-(n : ℤ)) := fun n => by
    have h2 := hs n (by simp [h])
    simp only [map_zero, sub_zero] at h2
    exact h2
  rw [adAt_apply]
  by_contra h0
  have h3 : Valued.v (afIso F E ((1 : E) ⊗ₜ[F] a) P) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (afIso F E ((1 : E) ⊗ₜ[F] a) P) = WithZero.exp m :=
    ⟨_, (WithZero.exp_log h3).symm⟩
  have h4 := h1 (m.natAbs + 1)
  rw [hm, WithZero.exp_le_exp] at h4
  omega

theorem adAt_eq_zero_of_prV (P : HeightOneSpectrum (𝓞 E)) (z : AfE F E) (h : prV (E := E) (P.under (𝓞 F)) z = 0) :
    adAt F P z = 0 := by
  classical
  let b := Module.finBasis F E
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b z
  have h1 : (c.mapRange (evalV F (P.under (𝓞 F))) (map_zero _)).sum (fun i n => b i ⊗ₜ[F] n) = 0 := by
    rw [Finsupp.sum_mapRange_index (fun i => TensorProduct.tmul_zero _ _)]
    rw [Finsupp.sum, map_sum] at h
    rw [Finsupp.sum]
    exact h
  have h2 := TensorProduct.sum_tmul_basis_left_eq_zero b _ h1
  have h3 : ∀ i, c i (P.under (𝓞 F)) = 0 := fun i => by
    have h4 := DFunLike.congr_fun h2 i
    have h5 : evalV F (P.under (𝓞 F)) (c i) = 0 := by simpa using h4
    exact h5
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have e : b i ⊗ₜ[F] c i = (b i ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] c i) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, map_mul, adAt_one_tmul_eq_zero P _ (h3 i), mul_zero]

end GenP

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

section GenR

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ}

theorem mulVec_inclE (M : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (M.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) =
      fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((M *ᵥ x) i) :=
  (RingHom.map_mulVec (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) M x |> funext).symm

theorem hatL_mulVec {L L' : Submodule (𝓞 E) (Sp E n)} (M : Matrix (Fin n) (Fin n) E) (h : ∀ x ∈ L, M *ᵥ x ∈ L')
    {y : Fin n → AfE F E} (hy : y ∈ Formalism.L2.Herm.hatL (F := F) L) :
    (M.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ y ∈ Formalism.L2.Herm.hatL (F := F) L' := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mulVec_inclE]
    exact Submodule.subset_span ⟨_, h x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have e : (M.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ (c • a) = c • ((M.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))) *ᵥ a) := by
      show _ *ᵥ ((c : AfE F E) • a) = (c : AfE F E) • _
      rw [Matrix.mulVec_smul]
    rw [e]
    exact Submodule.smul_mem _ _ ha

theorem ratAd_val (γ : UF E n) : (ratAd F γ : GL (Fin n) (AfE F E)).1 =
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := rfl

theorem ratAd_inv (γ : UF E n) : (ratAd F γ)⁻¹ = ratAd F γ⁻¹ := by
  unfold ratAd
  rw [map_inv, map_inv]

theorem ufGL_mulVec' (γ : UF E n) (x : Sp E n) : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = γ.1 x :=
  toGLm_mulVec γ.1 x

theorem pullV_rat (γ : UF E n) (g : GL (Fin n) (AfE F E)) (x : Sp E n) :
    pullV (ratAd F γ * g) x = pullV g (γ⁻¹.1 x) := by
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, ratAd_inv, ratAd_val, mulVec_inclE, ufGL_mulVec']

theorem mem_hatL_gmap (γ : UF E n) (L : Submodule (𝓞 E) (Sp E n)) (x : Fin n → AfE F E) :
    x ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.HermitianLatticesTheory.gmap γ.1 L) ↔ ((ratAd F γ)⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) L := by
  constructor
  · intro hx
    rw [ratAd_inv, ratAd_val]
    refine hatL_mulVec _ (fun y hy => ?_) hx
    rw [ufGL_mulVec']
    exact (mem_gmap _ _ _).1 hy
  · intro hx
    have h1 := hatL_mulVec (F := F) (L' := Formalism.HermitianLatticesTheory.gmap γ.1 L) ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) (fun y hy => by
      rw [ufGL_mulVec', mem_gmap]
      simpa using hy) hx
    rw [← ratAd_val, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1

theorem isPtOf_rat {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (γ : UF E n) :
    IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  refine ⟨?_, fun x => ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P i j => ?_⟩
  · refine mul_mem ?_ h.uni
    have hg : ufGL E n γ ∈ UJ (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) := by
      show cT _ _ * 1 * _ = 1
      rw [mul_one]
      exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul γ
    exact Formalism.UG.P.bc_mem (hc.sig : E →+* E) (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
      (by ext a; simp [sigR, inclE]) 1 _ hg
  · have e : ((ratAd F γ * g)⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x = (g⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ (((ratAd F γ)⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x) := by
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
    rw [e, ← h.lat]
    exact mem_hatL_gmap γ p.deco.1.N x
  · rw [pullV_rat]
    exact h.f P _ ((mem_gmap _ _ _).1 hx) i hi
  · rw [pullV_rat]
    have e : (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p).deco.1.be w x = p.deco.1.be w (γ⁻¹.1 x) := by
      show ((1 : GLG E n SG) w).1.mulVec _ = _
      simp
      rfl
    rw [e]
    exact h.be w _ ((mem_gmap _ _ _).1 hx) i
  · have e : (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p).fr P (Pi.single j 1) = γ.1 (p.fr P (Pi.single j 1)) := by
      show (γ.1 * p.1.2 P * (((1 : GLQ E n Q) P)⁻¹).1) _ = _
      simp
      rfl
    rw [e, ← ufGL_mulVec', Units.val_mul, Matrix.mul_apply, map_sum]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ratAd_val, Matrix.map_apply, adAt_inclE, h.fr]

end GenR

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

section GenT

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {N n : ℕ} (hN : N = n + 1)

theorem incl_coe_mem (r : 𝓞 E) : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E r) ∈ Formalism.L2.Herm.intAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨_, r, rfl⟩, rfl⟩)

theorem iniH_extM {A : Type} [CommRing A] (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) :
    iniH hN (extM hN g *ᵥ x) = g *ᵥ iniH hN x := funext fun i => extM_mulVec_iC hN g x i

def zext {A : Type} [Zero A] (a : Fin n → A) : Fin N → A := fun j => if h : j.1 < n then a ⟨j.1, h⟩ else 0

theorem iniH_zext {A : Type} [Zero A] (a : Fin n → A) : iniH hN (zext a : Fin N → A) = a := by
  funext i
  show (if h : i.1 < n then a ⟨i.1, h⟩ else 0) = a i
  rw [dif_pos i.2]

theorem zext_iL {A : Type} [Zero A] (a : Fin n → A) : (zext a : Fin N → A) (Br.iL hN) = 0 := by
  show (if h : n < n then a ⟨n, h⟩ else 0) = 0
  rw [dif_neg (lt_irrefl n)]

theorem hatL_ext {L : Submodule (𝓞 E) (Sp E n)} {M : Submodule (𝓞 E) (Sp E N)}
    (hM : ∀ x, x ∈ M ↔ iniH hN x ∈ L ∧ x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) (x : Fin N → AfE F E) :
    x ∈ Formalism.L2.Herm.hatL (F := F) M ↔ iniH hN x ∈ Formalism.L2.Herm.hatL (F := F) L ∧ x (Br.iL hN) ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x', hx', rfl⟩ := hy
      obtain ⟨h1, h2⟩ := (hM x').1 hx'
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 h2
      refine ⟨Submodule.subset_span ⟨_, h1, rfl⟩, ?_⟩
      show inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x' (Br.iL hN)) ∈ _
      rw [← hr]
      exact incl_coe_mem r
    | zero => exact ⟨Submodule.zero_mem _, zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨Submodule.add_mem _ ha.1 hb.1, add_mem ha.2 hb.2⟩
    | smul c a _ ha => exact ⟨Submodule.smul_mem _ c ha.1, mul_mem c.2 ha.2⟩
  · rintro ⟨h1, h2⟩
    have hJ : ∀ a ∈ Formalism.L2.Herm.hatL (F := F) L, (zext a : Fin N → AfE F E) ∈ Formalism.L2.Herm.hatL (F := F) M := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x', hx', rfl⟩ := hy
        refine Submodule.subset_span ⟨zext x', (hM _).2 ?_, ?_⟩
        · rw [iniH_zext, zext_iL]
          exact ⟨hx', zero_mem _⟩
        · funext j
          simp only [zext]
          split_ifs <;> simp
      | zero =>
        have : (zext (0 : Fin n → AfE F E) : Fin N → AfE F E) = 0 := by
          funext j
          simp only [zext]
          split_ifs <;> rfl
        rw [this]
        exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : (zext (a + b) : Fin N → AfE F E) = zext a + zext b := by
          funext j
          simp only [zext, Pi.add_apply]
          split_ifs <;> simp
        rw [this]
        exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : (zext (c • a) : Fin N → AfE F E) = c • zext a := by
          funext j
          simp only [zext, Pi.smul_apply]
          split_ifs <;> simp
        rw [this]
        exact Submodule.smul_mem _ c ha
    have he : (fun j => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single (Br.iL hN) 1 : Sp E N) j)) ∈ Formalism.L2.Herm.hatL (F := F) M := by
      refine Submodule.subset_span ⟨_, (hM _).2 ⟨?_, ?_⟩, rfl⟩
      · have : iniH hN (Pi.single (Br.iL hN) 1 : Sp E N) = 0 := by
          funext i
          have h3 : Br.iC hN i ≠ Br.iL hN := fun h => absurd (congrArg Fin.val h) i.2.ne
          show (Pi.single (Br.iL hN) 1 : Sp E N) (Br.iC hN i) = 0
          rw [Pi.single_eq_of_ne h3]
        rw [this]
        exact Submodule.zero_mem _
      · rw [Pi.single_eq_same]
        exact Submodule.one_le.1 le_rfl
    have e : x = zext (iniH hN x) + (⟨x (Br.iL hN), h2⟩ : Formalism.L2.Herm.intAf F E) •
        (fun j => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single (Br.iL hN) 1 : Sp E N) j)) := by
      funext j
      by_cases hj : j = Br.iL hN
      · subst hj
        rw [Pi.add_apply, zext_iL, zero_add, Pi.smul_apply, Pi.single_eq_same, map_one]
        exact (mul_one _).symm
      · have hj' : j.1 < n := by
          have h3 := j.2
          have h4 : j.1 ≠ n := fun h => hj (Fin.ext h)
          omega
        rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, map_zero]
        show _ = (if h : j.1 < n then iniH hN x ⟨j.1, h⟩ else 0) + _ * 0
        rw [dif_pos hj', mul_zero, add_zero]
        rfl
    rw [e]
    exact Submodule.add_mem _ (hJ _ h1) (Submodule.smul_mem _ _ he)

theorem std_ext (x : Sp E N) : x ∈ stdLat E N ↔ iniH hN x ∈ stdLat E n ∧ x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E) := by
  rw [mem_stdLat, mem_stdLat, Submodule.mem_one]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = Br.iL hN
    · rw [hj]; exact h2
    · have hj' : j.1 < n := by
        have h3 := j.2
        have h4 : j.1 ≠ n := fun h => hj (Fin.ext h)
        omega
      exact h1 ⟨j.1, hj'⟩

theorem carries_ext {L : Submodule (𝓞 E) (Sp E n)} {M : Submodule (𝓞 E) (Sp E N)}
    (hM : ∀ x, x ∈ M ↔ iniH hN x ∈ L ∧ x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) {y : GL (Fin n) (AfE F E)}
    (hy : Formalism.L2.Herm.Carries y (stdLat E n) L) : Formalism.L2.Herm.Carries (extGL hN y) (stdLat E N) M := by
  intro x
  rw [hatL_ext hN hM, hatL_ext hN (std_ext hN), extGL_inv_val, iniH_extM, extM_mulVec_iL]
  exact and_congr (hy _) Iff.rfl

theorem cT_extM {A : Type} [CommRing A] (σ : A →+* A) (g : Matrix (Fin n) (Fin n) A) : cT σ (extM hN g) = extM hN (cT σ g) := by
  subst hN
  ext a b
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last]
  · simp [extM_last_castSucc, extM_castSucc_last]
  · simp [extM_last_castSucc, extM_castSucc_last]
  · simp [extM_castSucc]

theorem extGL_mem_ustd {hc : Formalism.BasicNotions.CMData F E} {y : GL (Fin n) (AfE F E)} (hy : y ∈ Formalism.L2.Herm.UstdAf hc n) :
    extGL hN y ∈ Formalism.L2.Herm.UstdAf hc N := by
  have e1 : ∀ m : ℕ, (1 : Matrix (Fin m) (Fin m) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = 1 := fun m =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (y : Matrix (Fin n) (Fin n) (AfE F E)) *
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * y =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hy
  rw [e1, mul_one] at h1
  show cT (sigR hc.sig (FiniteAdeleRing (𝓞 F) F)) (extM hN y) *
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * extM hN y =
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
  rw [e1, mul_one, cT_extM, ← extM_mul, h1, extM_one]

theorem hasRes_sum {ι : Type} [Fintype ι] [DecidableEq ι] (P : HeightOneSpectrum (𝓞 E)) (a b : ι → P.adicCompletion E) (i : ι) (c : 𝓞 E ⧸ P.asIdeal) (r : 𝓞 E)
    (hi : HasRes P (a i) c) (ha : ∀ j, j ≠ i → HasRes P (a j) 0) (hb : ∀ j, Valued.v (b j) ≤ 1)
    (hbi : b i = algebraMap E _ (algebraMap (𝓞 E) E r)) :
    HasRes P (∑ j, a j * b j) (c * Ideal.Quotient.mk P.asIdeal r) := by
  obtain ⟨r0, rfl, h0⟩ := hi
  refine ⟨r0 * r, map_mul _ _ _, ?_⟩
  have e : ∑ j, a j * b j - algebraMap E _ (algebraMap (𝓞 E) E (r0 * r)) =
      ∑ j ∈ Finset.univ.erase i, a j * b j + (a i - algebraMap E _ (algebraMap (𝓞 E) E r0)) * b i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hbi, map_mul, map_mul]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun j hj => ?_) ?_
  · obtain ⟨s, hs, h1⟩ := ha j (Finset.ne_of_mem_erase hj)
    have h2 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E s)) < 1 := by
      rw [valued_algebraMap, HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact Ideal.Quotient.eq_zero_iff_mem.1 hs
    have h3 := Valuation.map_add_lt _ h1 h2
    rw [sub_add_cancel] at h3
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hb j)) h3
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hb i)) h0

end GenT

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

section GenU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem tilH_be {N n : ℕ} (hN : N = n + 1) {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet E n ∅ SG) {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) (w : SG) (x : Sp E N)
    (hx : x ∈ (DecoSet.tilH (ST := ST) hN pi d).1.N) :
    (∀ i : Fin n, (DecoSet.tilH (ST := ST) hN pi d).1.be w x (Br.iC hN i) = d.1.be w (iniH hN x) i) ∧
      (DecoSet.tilH (ST := ST) hN pi d).1.be w x (Br.iL hN) = redP w.1 (x (Br.iL hN) / algebraMap (𝓞 E) E pi) := by
  subst hN
  change x ∈ (DecoSet.til (ST := ST) pi d).1.N at hx
  show (∀ i : Fin n, (DecoSet.til (ST := ST) pi d).1.be w x i.castSucc = _) ∧ (DecoSet.til (ST := ST) pi d).1.be w x (Fin.last n) = _
  rw [DecoSet.til_val d hT hG] at hx ⊢
  have h1 : (d.1.til (ST := ST) pi).be w x = Fin.snoc (α := fun _ => 𝓞 E ⧸ w.1.asIdeal) (d.1.be w (initL E n x))
      (redP w.1 (x (Fin.last n) / algebraMap (𝓞 E) E pi)) := if_pos (le_locP _ _ hx)
  rw [h1]
  refine ⟨fun i => ?_, ?_⟩
  · rw [Fin.snoc_castSucc]
    rfl
  · rw [Fin.snoc_last]
    rfl

theorem isPtOf_tilFr {hc : Formalism.BasicNotions.CMData F E} {N n : ℕ} (hN : N = n + 1) {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    [IsEmpty Q] {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hpi1 : ∀ w : SG, pi - 1 ∈ w.1.asIdeal)
    {p : DecoF E n ∅ SG Q} {y : GL (Fin n) (AfE F E)} (hy : IsPtOf hc y p)
    {k : GL (Fin N) (AfE F E)} (hku : k ∈ Formalism.L2.Herm.UstdAf hc N) (hkl : Formalism.L2.Herm.Carries k (stdLat E N) (stdLat E N))
    (hkw : ∀ (w : SG) (i j : Fin N), adAt F w.1 ((k⁻¹ : GL (Fin N) (AfE F E)).1 i j) = (1 : Matrix (Fin N) (Fin N) (w.1.adicCompletion E)) i j)
    (hkT : ∀ (P : ST) (r j : Fin N), r.1 + 1 = N → HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin N) (AfE F E)).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (cO E pi) else 0)) :
    IsPtOf hc (extGL hN y * k) (tilFr (ST := ST) hN pi p) := by
  have hG : ∀ w : SG, pi ∉ w.1.asIdeal := fun w h => w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem h (hpi1 w)
    simpa using this))
  have hQ : ∀ P : Q, pi ∉ P.1.asIdeal := fun P => isEmptyElim P
  have hdeco := tilFr_deco (ST := ST) hN hT hG hQ p
  have hNm : ∀ x, x ∈ (tilFr (ST := ST) hN pi p).deco.1.N ↔ iniH hN x ∈ p.deco.1.N ∧ x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E) := by
    intro x
    rw [hdeco, tilH_N hN p.deco hT hG, Lsh_empty]
  have hcar := carries_ext hN hNm hy.lat
  have hpull : ∀ x, pullV (extGL hN y * k) x = (k⁻¹ : GL (Fin N) (AfE F E)).1 *ᵥ pullV (extGL hN y) x := by
    intro x
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
  have hint : ∀ x ∈ (tilFr (ST := ST) hN pi p).deco.1.N, pullV (extGL hN y) x ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E N) :=
    fun x hx => (hcar _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hlast : ∀ x, pullV (extGL hN y) x (Br.iL hN) = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x (Br.iL hN)) := by
    intro x
    unfold pullV
    rw [extGL_inv_val, extM_mulVec_iL]
  have hini : ∀ x (i : Fin n), pullV (extGL hN y) x (Br.iC hN i) = pullV y (iniH hN x) i := by
    intro x i
    unfold pullV
    rw [extGL_inv_val, extM_mulVec_iC]
    rfl
  have hcomp : ∀ (P : HeightOneSpectrum (𝓞 E)) x (i : Fin N), adAt F P (pullV (extGL hN y * k) x i) =
      ∑ j, adAt F P ((k⁻¹ : GL (Fin N) (AfE F E)).1 i j) * adAt F P (pullV (extGL hN y) x j) := by
    intro P x i
    rw [hpull]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine ⟨mul_mem (extGL_mem_ustd hN hy.uni) hku, fun x => ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P => isEmptyElim P⟩
  · have e : ((extGL hN y * k)⁻¹ : GL (Fin N) (AfE F E)).1 *ᵥ x =
        (k⁻¹ : GL (Fin N) (AfE F E)).1 *ᵥ (((extGL hN y)⁻¹ : GL (Fin N) (AfE F E)).1 *ᵥ x) := by
      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]
    rw [e, ← hkl]
    exact hcar x
  · have hi' : i = Br.iL hN := Fin.ext (by show i.1 = n; omega)
    subst hi'
    obtain ⟨-, h2⟩ := (hNm x).1 hx
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h2
    have hf : (tilFr (ST := ST) hN pi p).deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (cO E pi) * Ideal.Quotient.mk P.1.asIdeal r := by
      have hx' := hx
      rw [hdeco] at hx' ⊢
      rw [tilH_f hN p.deco hT hG P x hx', ← hr, ← map_mul]
      exact reduction_coe _ (cO E pi * r)
    rw [hf, hcomp]
    refine hasRes_sum P.1 _ _ (Br.iL hN) _ r ?_ (fun j hj => ?_) (fun j => DetSpec.val_le_of_mem_hatL P.1 (hint x hx) j) ?_
    · have := hkT P (Br.iL hN) (Br.iL hN) hi
      rwa [if_pos rfl] at this
    · have := hkT P (Br.iL hN) j hi
      rwa [if_neg hj] at this
    · rw [hlast, adAt_inclE, hr]
  · have hsum : adAt F w.1 (pullV (extGL hN y * k) x i) = adAt F w.1 (pullV (extGL hN y) x i) := by
      rw [hcomp, Finset.sum_eq_single i]
      · rw [hkw, Matrix.one_apply_eq, one_mul]
      · intro j _ hj
        rw [hkw, Matrix.one_apply_ne hj.symm, zero_mul]
      · simp
    rw [hsum]
    obtain ⟨h1, h2⟩ := (hNm x).1 hx
    have hbe := tilH_be hN p.deco hT hG w x (by rw [← hdeco]; exact hx)
    by_cases hi : i = Br.iL hN
    · subst hi
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 h2
      rw [hlast, adAt_inclE, hdeco, hbe.2, ← hr]
      have e : redP w.1 (algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E pi) = Ideal.Quotient.mk w.1.asIdeal r := by
        have h0 : algebraMap (𝓞 E) E pi ≠ 0 := fun h0 => hG w (by
          rw [RingOfIntegers.ext (h0.trans (map_zero _).symm : _)]
          exact zero_mem _)
        refine redP_eq w.1 (hG w) (mul_div_cancel₀ _ h0) ?_
        have h1 : Ideal.Quotient.mk w.1.asIdeal pi = 1 := by
          rw [← map_one (Ideal.Quotient.mk w.1.asIdeal)]
          exact Ideal.Quotient.eq.2 (hpi1 w)
        rw [h1, one_mul]
      rw [e]
      exact hasRes_coe _ _
    · have hi' : i.1 < n := by
        have h3 := i.2
        have h4 : i.1 ≠ n := fun h => hi (Fin.ext h)
        omega
      have e : i = Br.iC hN ⟨i.1, hi'⟩ := Fin.ext rfl
      rw [e, hini, hdeco, hbe.1]
      exact hy.be w _ h1 _

end GenU

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem isEmpty_functional_primes_base_tuple : IsEmpty ↥(QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) := by
  have h : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := I.twistPrimes_reference_tuple_eq_empty
  rw [h]
  infer_instance

theorem not_underQ (v : HeightOneSpectrum (𝓞 B.host.F)) : ¬ I.UnderQ I.mu0 v := by
  rintro ⟨P, hP, -⟩
  have h : I.Q I.mu0 = ∅ := I.twistPrimes_reference_tuple_eq_empty
  rw [h] at hP
  simp at hP

theorem pt_tilF (hI : I.Ok) (u : B.Word) (p : XPt (B.primes X) B.R I.sel (I.tup I.mu0)) {y : GA B (B.R.N B.R.m - 1)} {k : GA B (B.R.N B.R.m)}
    (hy : PtOf y p)
    (hk1 : ∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m))
    (hk2 : ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1)
    (hk3 : ∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = B.R.N B.R.m →
      HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B (B.R.N B.R.m)).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0)) :
    PtOf (extGL (N_m_succ B.R) y * k) (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup I.mu0) u p) := by
  haveI := isEmpty_functional_primes_base_tuple I
  obtain ⟨p0, hp0, hN0⟩ := hk1
  have hPr := (base_fields_primes_ok B X).2.1
  have hgw : ∀ w : (B.primes X).vGs, ∃ i, ((B.primes X).g i : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
    intro w
    have h1 : ∃ i, w.1 ∈ (B.primes X).vG i := by
      have h0 := w.2
      unfold Primes.vGs at h0
      simp only [Finset.mem_union] at h0
      rcases h0 with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    obtain ⟨i, hi⟩ := h1
    refine ⟨i, ?_⟩
    rw [← hPr.piG_norm i]
    exact w.1.asIdeal.mul_mem_left _ (mem_of_mem_divs hi)
  refine isPtOf_tilFr (N_m_succ B.R) (conj_piT_notMem hPr u) (fun w => ?_) hy hp0.uni ?_ ?_ hk3
  · obtain ⟨i, hi⟩ := hgw w
    obtain ⟨c, hc⟩ := hPr.piT_cong u
    rw [hc]
    refine w.1.asIdeal.mul_mem_right _ ?_
    have hd : (B.primes X).g i ∣ (B.primes X).cond * ((B.primes X).g 0 * (B.primes X).g 1) ^ 2 := by
      refine dvd_mul_of_dvd_right (dvd_pow ?_ two_ne_zero) _
      fin_cases i
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨c', hc'⟩ := hd
    rw [hc']
    push_cast
    exact w.1.asIdeal.mul_mem_right _ hi
  · have := hp0.lat
    rwa [hN0] at this
  · intro w i j
    have hT : (B.T u : 𝓞 B.host.F) ∉ (w.1.under (𝓞 B.host.F)).asIdeal := by
      intro hT
      obtain ⟨i, hi⟩ := hgw w
      have h1 : ((B.primes X).T u : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
        have h2 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.1.asIdeal := hT
        rw [map_natCast] at h2
        exact h2
      have hc : Nat.Coprime ((B.primes X).T u) ((B.primes X).g i) :=
        (Nat.coprime_primes (hPr.T_prime u) (hPr.g_prime i)).2 (hPr.T_ne_g u i)
      have h3 : ((1 : ℕ) : 𝓞 B.fields.E) ∈ w.1.asIdeal := by
        obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc)
        have e : ((1 : ℤ) : 𝓞 B.fields.E) = (a : 𝓞 B.fields.E) * ((B.primes X).T u : 𝓞 B.fields.E) +
            (b : 𝓞 B.fields.E) * ((B.primes X).g i : 𝓞 B.fields.E) := by
          rw [← hab]; push_cast; ring
        have e' : ((1 : ℕ) : 𝓞 B.fields.E) = ((1 : ℤ) : 𝓞 B.fields.E) := by simp
        rw [e', e]
        exact add_mem (w.1.asIdeal.mul_mem_left _ h1) (w.1.asIdeal.mul_mem_left _ hi)
      exact w.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h3))
    have h1 : bc (prV (E := B.host.E) (w.1.under (𝓞 B.host.F))) (k⁻¹ : GA B (B.R.N B.R.m)) = 1 := by
      rw [map_inv, hk2 _ hT, inv_one]
    have h2 : prV (E := B.host.E) (w.1.under (𝓞 B.host.F))
        ((k⁻¹ : GA B (B.R.N B.R.m)).1 i j - (1 : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)) i j) = 0 := by
      have h3 := congrArg (fun g : GL (Fin (B.R.N B.R.m)) _ => g.1 i j) h1
      simp only [Units.val_one] at h3
      have h4 : prV (E := B.host.E) (w.1.under (𝓞 B.host.F)) ((k⁻¹ : GA B (B.R.N B.R.m)).1 i j) =
        (1 : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) _) i j := h3
      rw [map_sub, h4, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h3 := adAt_eq_zero_of_prV w.1 _ h2
    rw [map_sub, sub_eq_zero] at h3
    refine h3.trans ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 1600000 in

theorem exists_ka (hI : I.Ok) (u : B.Word) {Lb : Unit → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {U : Unit → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u I.mu0 B.R.m).Cl → GA B (B.R.N B.R.m)}
    {st : ∀ c, (I.stp u I.mu0 B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E} {k : Unit → GA B (B.R.N B.R.m)}
    (hR : I.Reads u I.mu0 B.R.m (fun _ => ()) Lb U chi y st k) (c : (I.stX I.mu0).Cl) {y' : GA B (B.R.N B.R.m - 1)}
    (hy : PtOf y' ((I.stX I.mu0).rep c).1.1) :
    ∃ κ : U (),
      bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
        ((I.stp u I.mu0 B.R.m).gam _ ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))) *
          y ((I.perIn u I.mu0).tilC c) = extGL (N_m_succ B.R) y' * κ.1 ∧
      (((chi () κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 B.R.m).chr _
        ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)) : B.LLˣ) : B.LL) := by
  have hp := pt_tilF I hI u ((I.stX I.mu0).rep c).1.1 hy (hR.k_std ())
    (fun v hT => hR.k_off () v hT (not_underQ I v) (Or.inl rfl)) (hR.k_T ())
  have hm := (I.stp u I.mu0 B.R.m).mv_smul (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)
  obtain ⟨m, hmm⟩ : ∃ m, m = (I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c) := ⟨_, rfl⟩
  rw [← hmm] at hm ⊢
  have hp' : PtOf (ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (extGL (N_m_succ B.R) y' * k ())) _ := isPtOf_rat hp (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹
  let κ0 : (I.stp u I.mu0 B.R.m).G (I.perIn u I.mu0).b0 := (1, m.2.1, m.2.2)
  have hgam : (I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m))
  have hempty : ∀ p : (I.stp u I.mu0 B.R.m).D (I.perIn u I.mu0).b0, p.1.2 = ∅ := fun p => by
    have h := p.2
    rw [congrArg (fun y => y.ys p.1.1.deco.1.N) (ysAt_m B.R I.sel (I.tup I.mu0) (I.cst I.mu0))] at h
    exact h
  have hact : ((I.stp u I.mu0 B.R.m).act (I.perIn u I.mu0).b0 κ0 ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c))).1.1 =
      (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (I.Q I.mu0)) •
        (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup I.mu0) u ((I.stX I.mu0).rep c).1.1) := by
    have e1 : FrmG.incl _ _ m • ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)).1.1 =
        tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup I.mu0) u ((I.stX I.mu0).rep c).1.1 :=
      congrArg (fun d : (I.stp u I.mu0 B.R.m).D (I.perIn u I.mu0).b0 => d.1.1) hm
    rw [← e1]
    refine Eq.trans ?_ (smul_smul _ _ _).symm
    have e2 : FrmG.incl (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m (I.perIn u I.mu0).b0)
        (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m (I.perIn u I.mu0).b0) κ0 =
        (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (I.Q I.mu0)) *
        FrmG.incl _ _ m := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (inv_mul_cancel _).symm
      · exact (one_mul _).symm
      · exact (one_mul _).symm
    exact congrArg (fun a => a • ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)).1.1) e2
  have hcos : cosetIn ((I.stp u I.mu0 B.R.m).act (I.perIn u I.mu0).b0 κ0 ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c))) =
      cosetIn ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)) := by
    ext z
    simp [cosetIn, hempty]
  obtain ⟨x, hx⟩ : ∃ x : GA B (B.R.N B.R.m), x = (y ((I.perIn u I.mu0).tilC c))⁻¹ * ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * extGL (N_m_succ B.R) y' := ⟨_, rfl⟩
  have hxk : y ((I.perIn u I.mu0).tilC c) * x * k () = ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (extGL (N_m_succ B.R) y' * k ()) := by
    rw [hx]; group
  have hq : PtOf (y ((I.perIn u I.mu0).tilC c) * x * k ()) ((I.stp u I.mu0 B.R.m).act (I.perIn u I.mu0).b0 κ0 ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c))).1.1 := by
    rw [hxk, hact]
    exact hp'
  have hxU : x ∈ U () := (hR.lev ((I.perIn u I.mu0).tilC c) x _ hq).2 ⟨κ0, hgam, rfl, hcos⟩
  have hchr := hR.chr ((I.perIn u I.mu0).tilC c) ⟨x, hxU⟩ κ0 hgam hq
  refine ⟨⟨x, hxU⟩⁻¹, ?_, ?_⟩
  · have e : ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ =
        (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 m))⁻¹ := by
      unfold ratAd
      rw [map_inv, map_inv]
      rfl
    show _ = extGL (N_m_succ B.R) y' * x⁻¹
    rw [hx, e]
    group
  · rw [map_inv, inv_inv]
    exact hchr

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

section Gen3

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem til_L_eq {N n : ℕ} (hN : N = n + 1) {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {pi : 𝓞 E}
    (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal) (hpi : ∀ P : ST, pi ∈ P.1.asIdeal)
    (hdvd : ∀ r : 𝓞 E, (∀ P : ST, r ∈ P.1.asIdeal) → pi ∣ r) (d : DecoSet E n ∅ SG)
    (f : (Fin n → E) →ₗ[E] (Fin N → E)) (hf : ∀ x j, f x j = if h : j.1 < n then x ⟨j.1, h⟩ else 0)
    (z : Fin N → E) (hz : ∀ j, z j = if j.1 + 1 = N then (pi : E) else 0) :
    (DecoSet.tilH (ST := ST) hN pi d).1.L = d.1.N.map (f.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z} := by
  subst hN
  have e1 : f = incl E n := by
    refine LinearMap.ext fun x => funext fun j => ?_
    rw [hf]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [incl]
    · simp [incl]
  have e2 : z = z0 E n (algebraMap (𝓞 E) E pi) := by
    funext j
    rw [hz]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [z0, eLast]
    · have h1 : ¬ (i.1 + 1 = n + 1) := by omega
      have h2 : i.1 ≠ n := i.2.ne
      simp [z0, eLast, h1, h2, (Fin.castSucc_lt_last i).ne]
  rw [e1, e2]
  show (DecoSet.til (ST := ST) pi d).1.L = _
  rw [DecoSet.til_val d hT hG]
  exact d.2.til_L hT hG hpi hdvd

theorem L_act {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {d : Deco E n ST SG} (hd : d.Ok)
    {ga : Sp E n ≃ₗ[E] Sp E n} (hga : ga ∈ UF E n) (h : GLG E n SG) : (d.act ga h).L = Formalism.HermitianLatticesTheory.gmap ga d.L := by
  ext x
  rw [(hd.act hga h).mem_L, mem_gmap, hd.mem_L]
  exact and_congr (mem_gmap _ _ _) Iff.rfl

end Gen3

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def z0v (B : Base) (X : PreX B.toPre) (u : B.Word) : Fin (B.R.N B.R.m) → B.host.E :=
  fun j => if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0

theorem lastCoordinateUniformizerVector_eq_single (u : B.Word) : z0v B X u = Pi.single (Br.iL (N_m_succ B.R)) ((X.piT u : 𝓞 B.host.E) : B.host.E) := by
  funext j
  have h := N_m_succ B.R
  have e : j = Br.iL (N_m_succ B.R) ↔ j.1 + 1 = B.R.N B.R.m := by
    rw [Fin.ext_iff]
    show j.1 = B.R.N B.R.m - 1 ↔ _
    omega
  unfold z0v
  by_cases h1 : j.1 + 1 = B.R.N B.R.m
  · rw [if_pos h1, e.2 h1, Pi.single_eq_same]
  · rw [if_neg h1, Pi.single_eq_of_ne (fun h2 => h1 (e.1 h2))]

theorem hform_one_single {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι] (σ : A →+* A) (i : ι) (a : A) (y : ι → A) :
    hform σ (1 : Matrix ι ι A) (Pi.single i a) y = σ a * y i := by
  unfold hform
  rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne hb.symm]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

variable (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem hermitianForm_lastCoordinateUniformizerVector_self (hg : gramN (I.rec7 l Z) B.R.m le_rfl = 1) (u : B.Word) :
    hform (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) B.R.m le_rfl) (z0v B X u) (z0v B X u) =
      ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) := by
  rw [hg, lastCoordinateUniformizerVector_eq_single]
  refine (hform_one_single (A := B.host.E) (ι := Fin (B.R.N B.R.m)) (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (Br.iL (N_m_succ B.R)) _ _).trans ?_
  rw [Pi.single_eq_same]
  have h := congrArg (algebraMap (𝓞 B.fields.E) B.fields.E) ((base_fields_primes_ok B X).2.1.piT_norm u)
  rw [map_mul, map_natCast] at h
  rw [mul_comm]
  exact h

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

theorem line_of_orth {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) (σ : E →+* E) {w : Fin N → E} (hw : w ≠ 0)
    (f : (Fin n → E) → (Fin N → E)) (hf : ∀ x j, f x j = if h : j.1 < n then x ⟨j.1, h⟩ else 0)
    (h : ∀ x, hform σ (1 : Matrix (Fin N) (Fin N) E) (f x) w = 0) (a : E) :
    ∃ b : E, Pi.single (Br.iL hN) a = b • w := by
  have h0 : ∀ j : Fin n, w (Br.iC hN j) = 0 := fun j => by
    have e : f (Pi.single j 1) = Pi.single (Br.iC hN j) 1 := by
      funext i
      rw [hf]
      split_ifs with hi
      · by_cases e : i = Br.iC hN j
        · subst e
          rw [Pi.single_eq_same]
          have : (⟨(Br.iC hN j).1, hi⟩ : Fin n) = j := Fin.ext rfl
          rw [this, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne e, Pi.single_eq_of_ne]
          intro e2
          have e3 : i.1 = j.1 := congrArg Fin.val e2
          exact e (Fin.ext e3)
      · rw [Pi.single_eq_of_ne]
        intro e
        exact hi (by rw [e]; exact j.2)
    have h1 := h (Pi.single j 1)
    rw [e, hform_one_single, map_one, one_mul] at h1
    exact h1
  have hl : w (Br.iL hN) ≠ 0 := fun hl => hw (by
    funext i
    by_cases hi : i.1 < n
    · exact h0 ⟨i.1, hi⟩
    · have e : i = Br.iL hN := Fin.ext (by show i.1 = n; have := i.2; omega)
      rw [e]; exact hl)
  refine ⟨a / w (Br.iL hN), ?_⟩
  funext i
  by_cases e : i = Br.iL hN
  · subst e
    rw [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hl]
  · rw [Pi.single_eq_of_ne e, Pi.smul_apply, smul_eq_mul]
    have hi : i.1 < n := by
      have := i.2
      have h2 : i.1 ≠ n := fun h3 => e (Fin.ext h3)
      omega
    have := h0 ⟨i.1, hi⟩
    rw [show Br.iC hN ⟨i.1, hi⟩ = i from Fin.ext rfl] at this
    rw [this, mul_zero]

theorem hT_co {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    (S : HSpace E) {n : ℕ} (h : S.rank = n) (x y : S.V) :
    S.hT x y = hform (hc.sig : E →+* E) (S.gram.reindex (finCongr h) (finCongr h)) (Crd.co S h x) (Crd.co S h y) := by
  subst h
  refine (Formalism.L2.Herm.hT_crd hc S x y).trans ?_
  have e1 : S.gram.reindex (finCongr (rfl : S.rank = S.rank)) (finCongr rfl) = S.gram := by
    ext a b
    simp
  have e2 : ∀ v, Crd.co S rfl v = Formalism.L2.Herm.crd S v := fun v => by
    funext a
    simp [Crd.co, Formalism.L2.Herm.crd, LinearEquiv.funCongrLeft]
  rw [e1, e2, e2]

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))

theorem lastCoordinateUniformizerVector_spans_orthogonal_line (hg : gramN (I.rec7 l Z) B.R.m le_rfl = 1)
    (hiX : ∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) (u : B.Word) :
    ∃ a : (I.rec7 l Z).host.E, z0v B X u = a • zc (I.rec7 l Z) := by
  rw [lastCoordinateUniformizerVector_eq_single]
  refine line_of_orth (N_m_succ B.R) (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) ?_ (iXc (I.rec7 l Z)) hiX ?_ _
  · intro h0
    letI := (I.rec7 l Z).host.cmStar
    have h1 : (I.rec7 l Z).sp.z = 0 := (Crd.co ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) _ le_rfl)).map_eq_zero_iff.1 h0
    exact (I.rec7 l Z).sp.z_anis (by rw [h1]; simp)
  · intro x
    letI := (I.rec7 l Z).host.cmStar
    have h1 := (I.rec7 l Z).sp.z_orth ((Crd.co (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z))).symm x)
    rw [hT_co (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) _ le_rfl)] at h1
    have h2 : hform (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) B.R.m le_rfl) (iXc (I.rec7 l Z) x) (zc (I.rec7 l Z)) = 0 := h1
    rw [hg] at h2
    exact h2

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

section Gen4

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mulLat_toGLm {n : ℕ} (g : Sp E n ≃ₗ[E] Sp E n) (L : Submodule (𝓞 E) (Sp E n)) :
    Formalism.L2.Forms.mulLat ((toGLm E n g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) L = Formalism.HermitianLatticesTheory.gmap g L := by
  ext x
  unfold Formalism.L2.Forms.mulLat Formalism.HermitianLatticesTheory.gmap
  simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, toGLm_mulVec]
  rfl

theorem hform_one_eq_hStd {n : ℕ} (σ : E →+* E) (hσ : ∀ x, σ x = star x) (x y : Fin n → E) :
    hform σ (1 : Matrix (Fin n) (Fin n) E) x y = hStd E n x y := by
  rw [hStd_apply]
  unfold hform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [hσ]
  · intro b _ hb
    simp [Matrix.one_apply_ne hb.symm]
  · simp

theorem dualL_le_Lsh {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (σ : E →+* E) (hσ : ∀ x, σ x = star x) (d : Deco E n ST SG) :
    dualL σ (1 : Matrix (Fin n) (Fin n) E) d.L ≤ d.Lsh := by
  refine Submodule.span_le.2 fun y hy => ?_
  show y ∈ Formalism.HermitianLatticesTheory.dual (hStd E n) d.L
  rw [mem_dual]
  intro x hx
  obtain ⟨r, hr⟩ := hy x hx
  rw [← hform_one_eq_hStd σ hσ, ← hr]
  exact Submodule.mem_one.2 ⟨r, rfl⟩

end Gen4

theorem TDat.fv_mk {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (P : ST) (c : S.Cl) (h : A.fv P c ≠ 0) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  classical
  have h1 : ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
    by_contra h2
    exact h (dif_neg h2)
  have h2 : A.fv P c = h1.choose := dif_pos h1
  rw [h2]
  exact h1.choose_spec x

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem til_lat_eq (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (hiX : ∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) (u : B.Word) (c : (I.stX I.mu0).Cl) :
    Formalism.L2.Forms.mulLat (((I.stp u I.mu0 B.R.m).gam _ ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)) : GL _ _) : Matrix _ _ _)
      ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)).1.1.deco.1.L =
    (((I.stX I.mu0).rep c).1.1.deco.1.N).map ((iXc (I.rec7 l Z)).restrictScalars (𝓞 (I.rec7 l Z).host.E)) ⊔
      Submodule.span (𝓞 (I.rec7 l Z).host.E) {z0v B X u} := by
  have hPr := (base_fields_primes_ok B X).2.1
  have hm := (I.stp u I.mu0 B.R.m).mv_smul (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)
  obtain ⟨m, hmm⟩ : ∃ m, m = (I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c) := ⟨_, rfl⟩
  rw [← hmm] at hm ⊢
  have e0 : ((I.perIn u I.mu0).tilPt c).1.1.deco = DecoSet.tilH (N_m_succ B.R) ((B.primes X).piT u) ((I.stX I.mu0).rep c).1.1.deco :=
    PerLaw.til_deco hI u I.mu0 _ _
  have e1 : ((I.perIn u I.mu0).tilPt c).1.1.deco.1 =
      ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)).1.1.deco.1.act m.1.1 m.2.1.1 := by
    have := congrArg (fun d : (I.stp u I.mu0 B.R.m).D (I.perIn u I.mu0).b0 => d.1.1.deco.1) hm
    exact this.symm
  have e2 := L_act ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)).1.1.deco.2 m.1.2 m.2.1.1
  rw [← e1, e0, til_L_eq (N_m_succ B.R) (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) (fun P => decoFin_mem_of_mem_divs P.2)
    (piT_dvd_of_mem (base_fields_primes_ok B X).1 hPr u) _ (iXc (I.rec7 l Z)) hiX (z0v B X u) (fun j => rfl)] at e2
  exact (mulLat_toGLm m.1.1 _).trans e2.symm

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 1600000 in

theorem til_fv_eq (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (hg : gramN (I.rec7 l Z) B.R.m le_rfl = 1) (u : B.Word)
    (hsu : ∀ c, clsCrd (I.rec7 l Z) u B.R.m le_rfl c = ((I.stp u I.mu0 B.R.m).rep c).1.1.deco.1.L)
    (A : AtTTied (D := I.rec7 l Z) u) (L : LvTied (D := I.rec7 l Z) u A B.R.m le_rfl) (hres : A.res = I.resT l u I.mu0)
    (hL : ∀ v c (z : Ld (I.rec7 l Z) u B.R.m le_rfl c) (h : z.1 ∈ ((I.stp u I.mu0 B.R.m).rep c).1.1.deco.1.N),
      L.pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩)
    (v : ((I.rec7 l Z).mem u).A.vT) (c : (I.stX I.mu0).Cl) (x : ↥(Ld (I.rec7 l Z) u B.R.m le_rfl (((I.rec7 l Z).fm u).til c)))
    (r : 𝓞 (I.rec7 l Z).host.E)
    (hr : (r : (I.rec7 l Z).host.E) = hform (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) B.R.m le_rfl) (z0v B X u)
      (((I.stp u I.mu0 B.R.m).gam _ ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ x.1)) :
    ((I.rec7 l Z).fm u).fv B.R.m v (((I.rec7 l Z).fm u).til c) (L.pr v _ x) = A.res v r := by
  have hPr := (base_fields_primes_ok B X).2.1
  have hm := (I.stp u I.mu0 B.R.m).mv_smul (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)
  obtain ⟨m, hmm⟩ : ∃ m, m = (I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c) := ⟨_, rfl⟩
  rw [← hmm] at hm hr
  have hx1 : x.1 ∈ ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)).1.1.deco.1.Lsh := by
    have h1 := x.2
    have h2 : x.1 ∈ dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) B.R.m le_rfl)
      (clsCrd (I.rec7 l Z) u B.R.m le_rfl (((I.rec7 l Z).fm u).til c)) := h1
    rw [hg] at h2
    have h3 := Eq.mp (congrArg (fun M => x.1 ∈ dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) 1 M)
      (hsu (((I.rec7 l Z).fm u).til c))) h2
    exact dualL_le_Lsh (E := B.host.E) _ (fun _ => rfl) _ h3
  obtain ⟨xv, hxv⟩ : ∃ xv : Sp B.fields.E (B.R.N B.R.m), xv = x.1 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 B.fields.E, s = cO B.fields.E ((B.primes X).piT u) := ⟨_, rfl⟩
  have hsN : s • xv ∈ ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)).1.1.deco.1.N := by
    refine ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)).1.1.deco.2.smul_Lsh_mem_N (fun P => ?_) (hxv ▸ hx1)
    rw [hs, cO_cO]
    exact decoFin_mem_of_mem_divs P.2
  have h0 : ((show 𝓞 (I.rec7 l Z).host.E from s) • x).1 = s • xv := by rw [hxv]; rfl
  have h1 := hL v _ ((show 𝓞 (I.rec7 l Z).host.E from s) • x) (h0 ▸ hsN)
  have h2 := L.pr_smul v _ (show 𝓞 (I.rec7 l Z).host.E from s) x
  have hne := ((l.fmL u I.mu0).lev B.R.m).fv_ne v ((I.perIn u I.mu0).tilC c)
  have h3 := TDat.fv_mk ((I.atIn u I.mu0).A B.R.m) v ((I.perIn u I.mu0).tilC c) hne ⟨s • xv, hsN⟩
  have hlev := (l.lev u I.mu0).lev B.R.m
  have h4 := hlev.f_act (I.perIn u I.mu0).b0 m ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)) v (s • xv)
  have h5 := (hlev.N_act (I.perIn u I.mu0).b0 m ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)) (s • xv)).2 hsN
  have h4' := congrArg (fun d => ((I.atIn u I.mu0).A B.R.m).f (I.perIn u I.mu0).b0 d v
    (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 m).1 *ᵥ (s • xv))) hm
  have h5' := Eq.mp (congrArg (fun d => ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 m).1 *ᵥ (s • xv) ∈
    ((I.atIn u I.mu0).A B.R.m).N (I.perIn u I.mu0).b0 d) hm) h5
  have h6 := (l.ovr u I.mu0).f_til c.1 ((I.stX I.mu0).rep c) v _ h5'
  obtain ⟨rv, hrv⟩ : ∃ rv : 𝓞 B.fields.E, rv = r := ⟨_, rfl⟩
  have hr' : algebraMap (𝓞 B.fields.E) B.fields.E rv = star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) *
      (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 m).1 *ᵥ xv) (Br.iL (N_m_succ B.R)) := by
    rw [hg, lastCoordinateUniformizerVector_eq_single] at hr
    rw [hrv, hxv]
    refine hr.trans ((hform_one_single (A := B.host.E) (ι := Fin (B.R.N B.R.m)) _ (Br.iL (N_m_succ B.R)) _ _).trans ?_)
    rfl
  have h7 : ((I.perIn u I.mu0).tz * (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 m).1 *ᵥ (s • xv)) (Br.iL (N_m_succ B.R))) =
      algebraMap (𝓞 B.fields.E) B.fields.E (s * rv) := by
    have e1 : (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 m).1 *ᵥ (s • xv)) (Br.iL (N_m_succ B.R)) =
        algebraMap (𝓞 B.fields.E) B.fields.E s * (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 m).1 *ᵥ xv) (Br.iL (N_m_succ B.R)) := by
      rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
    rw [e1, map_mul, hr']
    show star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) * _ = _
    ring
  have h8 : ((I.atIn u I.mu0).A B.R.m).f (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).rep ((I.perIn u I.mu0).tilC c)) v (s • xv) =
      Ideal.Quotient.mk v.1.asIdeal (s * rv) := by
    refine h4.symm.trans (h4'.trans (h6.trans ?_))
    rw [h7]
    exact reduction_coe _ _
  have hresv : A.res v = Ideal.Quotient.mk v.1.asIdeal := congrFun hres v
  subst hxv hrv
  have hs0 : Ideal.Quotient.mk v.1.asIdeal s ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, hs]
    exact conj_piT_notMem hPr u v
  obtain ⟨pv, hpv⟩ : ∃ pv : ((I.atIn u I.mu0).A B.R.m).lv v ((I.perIn u I.mu0).tilC c), pv = L.pr v _ x := ⟨_, rfl⟩
  have h2' : (L.pr v _ ((show 𝓞 (I.rec7 l Z).host.E from s) • x) : ((I.atIn u I.mu0).A B.R.m).lv v ((I.perIn u I.mu0).tilC c)) =
      (Ideal.Quotient.mk v.1.asIdeal s : Res v.1) • pv := by
    rw [hpv]
    have h2a := h2
    rw [hresv] at h2a
    exact h2a
  have h9 : ((I.atIn u I.mu0).A B.R.m).fv v ((I.perIn u I.mu0).tilC c) ((Ideal.Quotient.mk v.1.asIdeal s : Res v.1) • pv) =
      Ideal.Quotient.mk v.1.asIdeal (s * rv) := by
    exact (congrArg (fun w => ((I.atIn u I.mu0).A B.R.m).fv v ((I.perIn u I.mu0).tilC c) w) (h2'.symm.trans h1)).trans (h3.trans h8)
  rw [map_smul, smul_eq_mul, map_mul] at h9
  rw [hresv, ← hpv]
  exact mul_left_cancel₀ (M₀ := Res v.1) hs0 h9

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

section Gen6

variable {E R : Type} [Field E] [CommRing R] {N n : ℕ} (hN : N = n + 1)

theorem eq_extM_of_ext (φ : E →+* R) {a : E} (ha : a ≠ 0) {M : Matrix (Fin N) (Fin n) E}
    (hM : ∀ b j, M b j = if b = Br.iC hN j then 1 else 0) {g' : Matrix (Fin n) (Fin n) R} {g : Matrix (Fin N) (Fin N) R}
    (h1 : g * M.map φ = M.map φ * g') (h2 : g *ᵥ (fun b => φ ((Pi.single (Br.iL hN) a : Fin N → E) b)) = fun b => φ ((Pi.single (Br.iL hN) a : Fin N → E) b)) :
    g = extM hN g' := by
  subst hN
  have hphi : φ a * φ a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  refine eq_extM rfl (fun b j => ?_) (fun b => ?_)
  · have e := congrFun (congrFun h1 b) j
    rw [Matrix.mul_apply, Matrix.mul_apply] at e
    have e1 : ∑ l, g b l * (M.map φ) l j = g b (Br.iC rfl j) := by
      rw [Finset.sum_eq_single (Br.iC rfl j)]
      · simp [hM]
      · intro l _ hl
        simp [hM, hl]
      · simp
    rw [e1] at e
    rw [e]
    refine Fin.lastCases ?_ (fun i => ?_) b
    · have h3 : ∀ l : Fin n, Fin.last n ≠ Br.iC (rfl : n + 1 = n + 1) l := fun l => (Fin.castSucc_lt_last l).ne'
      simp [hM, h3, extM_last_castSucc]
      exact (extM_last_castSucc g' j).symm
    · have h3 : ∀ l : Fin n, (i.castSucc = Br.iC (rfl : n + 1 = n + 1) l) ↔ i = l := fun l => Fin.castSucc_inj
      simp [hM, h3]
      exact (extM_castSucc g' i j).symm
  · have e : ∀ b, g b (Fin.last n) * φ a = φ ((Pi.single (Fin.last n) a : Fin (n + 1) → E) b) := fun b => by
      have e := congrFun h2 b
      simp only [Matrix.mulVec, dotProduct] at e
      rw [Finset.sum_eq_single (Br.iL rfl)] at e
      · rw [Pi.single_eq_same] at e
        exact e
      · intro l _ hl
        rw [Pi.single_eq_of_ne hl, map_zero, mul_zero]
      · simp
    show g b (Fin.last n) = extM rfl g' b (Fin.last n)
    refine Fin.lastCases ?_ (fun i => ?_) b
    · have e' := e (Fin.last n)
      rw [Pi.single_eq_same] at e'
      rw [extM_last_last]
      have h3 := congrArg (· * φ a⁻¹) e'
      simp only [mul_assoc, hphi, mul_one] at h3
      exact h3
    · have e' := e i.castSucc
      rw [Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne, map_zero] at e'
      rw [extM_castSucc_last]
      have h3 := congrArg (· * φ a⁻¹) e'
      simp only [mul_assoc, hphi, mul_one, zero_mul] at h3
      exact h3

end Gen6

theorem iXm_apply {D : D7} (hiX : ∀ x j, iXc D x j = if h : j.1 < D.R.N D.R.m - 1 then x ⟨j.1, h⟩ else 0)
    (hN : D.R.N D.R.m = (D.R.N D.R.m - 1) + 1) (b : Fin (D.R.N D.R.m)) (j : Fin (D.R.N D.R.m - 1)) :
    iXm D b j = if b = Br.iC hN j then 1 else 0 := by
  have e : iXm D b j = iXc D (Pi.single j 1) b := by
    unfold iXm
    rw [LinearMap.toMatrix'_apply]
  rw [e, hiX]
  split_ifs with h1 h2 h2
  · subst h2
    have : (⟨(Br.iC hN j).1, h1⟩ : Fin (D.R.N D.R.m - 1)) = j := Fin.ext rfl
    rw [this, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne]
    intro e2
    have e3 : b.1 = j.1 := congrArg Fin.val e2
    exact h2 (Fin.ext e3)
  · exact absurd (by rw [h2]; exact j.2) h1
  · rfl

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

theorem frMul_inv_eq {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (γ : GL (Fin n) E)
    (s s' : Fr emb σ n) (h : ∀ τ, s.1 τ = (γ : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * s'.1 τ) :
    frMul emb σ γ⁻¹ s = s' := by
  refine Subtype.ext (funext fun τ => ?_)
  show ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ) * s.1 τ = s'.1 τ
  rw [h τ, ← mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), one_mul]

end GlobalTheory.Mem.Col2.TilX

namespace GlobalTheory.Mem.Col2.TilX

variable {B : Base} {X : PreX B.toPre}

theorem baseL_sup (u : B.Word) {Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m - 1) → B.host.E)}
    (h : ∀ x, x ∈ Lb ↔ x ∈ baseL B (B.R.N B.R.m) (X.piT u)) (h' : ∀ x, x ∈ Lb' ↔ x ∈ baseL B (B.R.N B.R.m - 1) 1)
    (f : (Fin (B.R.N B.R.m - 1) → B.host.E) →ₗ[B.host.E] (Fin (B.R.N B.R.m) → B.host.E))
    (hf : ∀ x j, f x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) :
    Lb = Lb'.map (f.restrictScalars (𝓞 B.host.E)) ⊔ Submodule.span (𝓞 B.host.E) {z0v B X u} := by
  have hN := N_m_succ B.R
  apply le_antisymm
  · intro x hx
    obtain hx' := (h x).1 hx
    have h1 : iniH hN x ∈ Lb' := (h' _).2 fun j => by
      obtain ⟨r, hr, -⟩ := hx' (Br.iC hN j)
      exact ⟨r, hr, fun _ => one_dvd _⟩
    obtain ⟨r, hr, hd⟩ := hx' (Br.iL hN)
    obtain ⟨t, rfl⟩ := hd (by show B.R.N B.R.m - 1 + 1 = _; omega)
    have e : x = f (iniH hN x) + t • z0v B X u := by
      funext j
      rw [Pi.add_apply, hf, Pi.smul_apply, lastCoordinateUniformizerVector_eq_single]
      by_cases hj : j.1 < B.R.N B.R.m - 1
      · rw [dif_pos hj, Pi.single_eq_of_ne (fun e => by rw [e] at hj; exact lt_irrefl _ hj), smul_zero, add_zero]
        rfl
      · have e : j = Br.iL hN := Fin.ext (by show j.1 = B.R.N B.R.m - 1; have := j.2; omega)
        subst e
        rw [dif_neg hj, Pi.single_eq_same, zero_add, hr, Algebra.smul_def]
        show algebraMap (𝓞 B.host.E) B.host.E (X.piT u * t) = _
        rw [map_mul, mul_comm]
    rw [e]
    exact Submodule.add_mem_sup ⟨_, h1, rfl⟩ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine sup_le ?_ ((Submodule.span_singleton_le_iff_mem _ _).2 ((h _).2 fun j => ?_))
    · rintro _ ⟨x, hx, rfl⟩
      refine (h _).2 fun j => ?_
      obtain hx' := (h' x).1 hx
      show ∃ r : 𝓞 B.host.E, f x j = (r : B.host.E) ∧ _
      rw [hf]
      split_ifs with hj
      · obtain ⟨r, hr, -⟩ := hx' ⟨j.1, hj⟩
        refine ⟨r, hr, fun e => ?_⟩
        omega
      · exact ⟨0, by simp, fun _ => dvd_zero _⟩
    · unfold z0v
      by_cases hj : j.1 + 1 = B.R.N B.R.m
      · exact ⟨X.piT u, by rw [if_pos hj], fun _ => dvd_rfl⟩
      · exact ⟨0, by rw [if_neg hj]; simp, fun e => absurd e hj⟩

end GlobalTheory.Mem.Col2.TilX

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Col2.TC.til_ties : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (A : AtTTied (D := (I.rec7 l Z)) u) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl) (KP : ClsPTied (D := (I.rec7 l Z)) u) (L : LvTied (D := (I.rec7 l Z)) u A B.R.m le_rfl) (W : ValTied (D := (I.rec7 l Z)) u A.eV B.R.m le_rfl K), A.res = I.resT l u I.mu0 → (∃ k, I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k) → I.ReadsP I.mu0 KP.lev.Lb KP.lev.U KP.lev.chi (fun c => (KP.y c).1) KP.lat (fun c s => (KP.stabI c s).1) → (∀ v c (z : Ld (I.rec7 l Z) u B.R.m le_rfl c) (h : z.1 ∈ ((I.stp u I.mu0 B.R.m).rep c).1.1.deco.1.N), L.pr v c z = Submodule.Quotient.mk ⟨z.1, h⟩) → I.IdY l Z u I.mu0 B.R.m le_rfl W.eY → ∃ (Tl : TilTied (D := (I.rec7 l Z)) u A KP L) (Ta : TilAd Tl K), (∀ j, Tl.z0 j = if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) ∧ TilBaseLat Tl K ∧ ∃ e, (∀ z, e z = z) ∧ EvzTie (D := (I.rec7 l Z)) Ta W e := by
  intro B X I hI hP l Z u A K KP L W hres hRd hRP hL hY
  obtain ⟨k, hk⟩ := hRd
  obtain ⟨-, -, hiX, hsp⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  obtain ⟨hg, -, hsu⟩ := hsp B.R.m le_rfl
  have hcls := (hsu u I.mu0).1
  have hN := N_m_succ B.R
  have hPr := (base_fields_primes_ok B X).2.1
  have hga : ∀ c, (I.stp u I.mu0 B.R.m).gam _ ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)) ∈
      UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) B.R.m le_rfl) := by
    intro c
    rw [hg]
    show cT _ _ * 1 * _ = 1
    rw [mul_one]
    exact ((l.ch u I.mu0).step B.R.m).unit _ _
  let Tl : TilTied (D := I.rec7 l Z) u A KP L :=
    { z0 := TilX.z0v B X u
      lastCoordinateUniformizerVector_spans_orthogonal_line := TilX.lastCoordinateUniformizerVector_spans_orthogonal_line I l Z hg hiX u
      hermitianForm_lastCoordinateUniformizerVector_self := TilX.hermitianForm_lastCoordinateUniformizerVector_self I l Z hg u
      ga := fun c => ⟨_, hga c⟩
      til_lat := fun c =>
        (congrArg (Formalism.L2.Forms.mulLat _) (hcls ((I.perIn u I.mu0).tilC c))).trans
          ((TilX.til_lat_eq I hI l Z hiX u c).trans (by rw [hRP.lat c]; rfl))
      til_fv := fun v c x r hr => TilX.til_fv_eq I hI l Z hg u hcls A L hres hL v c x r hr }
  choose ka hka1 hka2 using fun c => TilX.exists_ka I hI u hk c (hRP.pt c)
  have hpi0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
    intro h0
    have h1 : X.piT u = 0 := RingOfIntegers.ext h0
    have h2 := hPr.piT_norm u
    have h3 : (B.primes X).piT u = 0 := h1
    rw [h3, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  let Ta : TilAd Tl K :=
    { ka := ka
      til_ad := fun c g hg' => by
        have e : g.1 = TilX.extM hN (KP.y c).1.1 := by
          refine TilX.eq_extM_of_ext hN (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) hpi0
            (TilX.iXm_apply hiX hN) hg'.1 ?_
          have h2 := hg'.2
          rw [show Tl.z0 = _ from TilX.lastCoordinateUniformizerVector_eq_single u] at h2
          exact h2
        have e' : g = TilX.extGL hN (KP.y c).1 := Units.ext e
        rw [e']
        exact hka1 c }
  refine ⟨Tl, Ta, fun j => rfl, ?_, LinearEquiv.refl ℂ _, fun _ => rfl, ?_⟩
  · exact TilX.baseL_sup u (hk.lb ()) hRP.lb (iXc (I.rec7 l Z)) hiX
  · intro φ c s s' hs
    have hy1 : (W.eY s).1 = s.1 := hY s
    have hy2 : (W.eY s').1 = s'.1 := hY s'
    have hemb : ∀ τ, Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (Tl.ga c).1.1 τ =
        (((I.stp u I.mu0 B.R.m).gam _ ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1).map (embAt B.embLL B.fields.emb τ) := fun τ =>
      congrArg (fun f : B.host.E →+* ℂ => ((I.stp u I.mu0 B.R.m).gam _ ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1.map f) (B.fields_embC τ).symm
    have e1 := TilX.frMul_inv_eq B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam _ ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))) s s'
      (fun τ => (congrFun hy1 τ).symm.trans ((hs τ).trans (congrArg₂ (· * ·) (hemb τ) (congrFun hy2 τ))))
    have e2 := trFr_apply B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam _ ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))
      ((I.stp u I.mu0 B.R.m).chr _ ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))) (φ ((I.perIn u I.mu0).tilC c)) s
    rw [e1, ← hka2 c] at e2
    exact e2

end
