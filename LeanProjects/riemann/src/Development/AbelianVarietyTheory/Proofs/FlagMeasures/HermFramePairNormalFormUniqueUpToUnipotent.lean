import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open Formalism.HermitianLatticeCounting.P
namespace GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def Cmp (H : HermSpace K V) (p q : V × V) : Prop := H.B p.1 q.1 = H.B p.2 q.2

theorem Cmp.symm {p q : V × V} (h : Cmp H p q) : Cmp H q p := by
  unfold Cmp at *
  rw [← H.herm, h, H.herm]

theorem cmp_span_left {S : Set (V × V)} {q : V × V} (h : ∀ p ∈ S, Cmp H p q) :
    ∀ p ∈ Submodule.span K S, Cmp H p q := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [Cmp]
  | add x y _ _ h1 h2 => simp only [Cmp] at *; simp [h1, h2]
  | smul a x _ h1 => simp only [Cmp] at *; simp [h1]

theorem exists_isometry (S : Set (V × V)) (h : ∀ p ∈ S, ∀ q ∈ S, Cmp H p q)
    (h1 : (Submodule.span K S).map (LinearMap.fst K V V) = ⊤)
    (h2 : (Submodule.span K S).map (LinearMap.snd K V V) = ⊤) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, H.B (s x) (s y) = H.B x y) ∧ ∀ p ∈ S, s p.1 = p.2 := by
  have hG : ∀ p ∈ Submodule.span K S, ∀ q ∈ Submodule.span K S, Cmp H p q := fun p hp q hq =>
    cmp_span_left (fun p hp => (cmp_span_left (fun q hq => h q hq p hp) q hq).symm) p hp
  set G := Submodule.span K S with hGdef
  have s1 : ∀ v : V, ∃ p : G, p.1.1 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h1.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have s2 : ∀ v : V, ∃ p : G, p.1.2 = v := fun v => by
    obtain ⟨p, hp, e⟩ := Submodule.mem_map.1 (h2.symm ▸ Submodule.mem_top (x := v))
    exact ⟨⟨p, hp⟩, e⟩
  have b1 : Function.Bijective ((LinearMap.fst K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s1⟩
    have e1 : p.1.1 = 0 := hp
    refine Subtype.ext (Prod.ext e1 (H.nondeg _ fun y => ?_))
    obtain ⟨q, rfl⟩ := s2 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this.symm
  have b2 : Function.Bijective ((LinearMap.snd K V V).comp G.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun p hp => ?_, s2⟩
    have e1 : p.1.2 = 0 := hp
    refine Subtype.ext (Prod.ext (H.nondeg _ fun y => ?_) e1)
    obtain ⟨q, rfl⟩ := s1 y
    have := hG _ p.2 _ q.2
    rw [Cmp, e1] at this
    simpa using this
  have key : ∀ p : G, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) p.1.1 = p.1.2 := by
    intro p
    have : (LinearEquiv.ofBijective _ b1).symm p.1.1 = p := (LinearEquiv.symm_apply_eq _).2 rfl
    rw [LinearEquiv.trans_apply, this]
    rfl
  refine ⟨_, fun x y => ?_, fun p hp => key ⟨p, Submodule.subset_span hp⟩⟩
  obtain ⟨p, rfl⟩ := s1 x
  obtain ⟨q, rfl⟩ := s1 y
  rw [key, key]
  exact Eq.symm (hG _ p.2 _ q.2)

theorem gram_eq {F G : FlagD H r} (hT : F.T = G.T) (a b : Fin (r + 1)) :
    H.B (F.e a) (F.e b) = H.B (G.e a) (G.e b) := by
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · rw [F.zz, G.zz, hT]
  · rw [B_swap0 H (F.zperp b), B_swap0 H (G.zperp b)]
  · rw [F.zperp, G.zperp]
  · rw [F.iso, G.iso]

theorem flag_vector_mem_base_lattice (F F' : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F F' :=
  Fin.lastCases (lastVector_mem_jointSpan_left F F') (fun a => isotropicSpan_le_jointSpan_left _ _ (e_mem_X _ a)) a

theorem hermFlag_secondFrame_mem_frameSpan (F F' : FlagD H r) (a : Fin (r + 1)) : F'.e a ∈ V0 F F' :=
  Fin.lastCases (lastVector_mem_jointSpan_right F F') (fun a => isotropicSpan_le_jointSpan_right _ _ (e_mem_X _ a)) a

theorem perp_transfer {F G : FlagD H r} (h : SameGr F G) {w : V} (hw : ∀ a, H.B (F.e a) w = 0) (a : Fin (r + 1)) :
    H.B (G.e a) w = 0 := by
  have h1 := perp_X F (fun b => hw b.castSucc) _ (Xa_le_X F _ (h a))
  simpa [hw a] using h1

variable [NumberField K]

theorem wt_e (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F.e a) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_left (flag_vector_mem_base_lattice _ _ a))

theorem wt_e' (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F'.e a) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_left (hermFlag_secondFrame_mem_frameSpan _ _ a))

theorem wt_ist (N : NF H r) {w : V} (hw : w ∈ N.Wt) (b : Fin r) (hb : N.j ≤ b.val) : H.B (N.ist b) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))

variable [FiniteDimensional K V]

theorem decomp (N : NF H r) {w : V} (hw : ∀ a, H.B (N.F.e a) w = 0) : ∃ w' ∈ N.Wt, w' - w ∈ N.F.X := by
  obtain ⟨x, hx, hp⟩ := (NFGeom.full N).2.2.2.2.2.2.2.1 w hw
  obtain ⟨u, hu, i, hi, e⟩ := Submodule.mem_sup.1 ((NFGeom.isLift N).2.2 _ hp)
  refine ⟨u, hu, ?_⟩
  have : u - w = -(x + i) := by rw [← sub_eq_zero, ← sub_eq_zero.2 e]; abel
  rw [this]
  exact Submodule.neg_mem _ (Submodule.add_mem _ hx hi.1)

theorem eq_top (N : NF H r) (M : Submodule K V) (h1 : ∀ a, N.F.e a ∈ M) (h2 : ∀ a, N.F'.e a ∈ M)
    (h3 : ∀ b : Fin r, N.j ≤ b.val → N.ist b ∈ M) (h4 : N.Wt ≤ M) : M = ⊤ := by
  rw [eq_top_iff, ← (NFGeom.isCompl N).sup_eq_top, NFGeom.Pi_eq]
  refine sup_le h4 (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_) <;> refine Submodule.span_le.2 ?_
  · rintro _ ⟨b, -, rfl⟩; exact h1 _
  · rintro _ ⟨b, -, rfl⟩; exact h2 _
  · rintro _ (rfl | rfl)
    · exact h1 _
    · exact h2 _
  · rintro _ ⟨b, hb, rfl⟩; exact h3 b hb

theorem main (N₀ N₁ : NF H r) (h : SameGr N₀.F N₁.F) (hj : N₀.j = N₁.j) (hc : N₀.c = N₁.c) (hT : N₀.T = N₁.T)
    (hM : pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j) :
    ∃ s : V ≃ₗ[K] V, N₀.F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  have hX : N₁.F.X = N₀.F.X := AdaptInv.x_eq h
  have ee := gram_eq (F := N₀.F) (G := N₁.F) (by rw [N₀.hT, N₁.hT, hT])
  have e'e' := gram_eq (F := N₀.F') (G := N₁.F') (by rw [N₀.hT', N₁.hT', hT])
  have ee' : ∀ a b, H.B (N₀.F.e a) (N₀.F'.e b) = H.B (N₁.F.e a) (N₁.F'.e b) := by
    intro a b
    by_cases hb : N₀.j ≤ b.val
    · rw [N₀.same b hb, N₁.same b (hj ▸ hb)]
      simp [ee, hc]
    by_cases ha : N₀.j ≤ a.val
    · rw [NFGeom.e_eq N₀ a ha, NFGeom.e_eq N₁ a (hj ▸ ha)]
      simp [e'e', hc]
    have := congrFun (congrFun hM a) b
    simpa [pairM, ← hj, not_le.1 ha, not_le.1 hb] using this
  have ei : ∀ a (b : Fin r), N₀.j ≤ b.val → H.B (N₀.F.e a) (N₀.ist b) = H.B (N₁.F.e a) (N₁.ist b) := by
    intro a b hb
    refine Fin.lastCases ?_ (fun a => ?_) a
    · exact (N₀.normalForm_dual_orthogonal_last b hb).trans (N₁.normalForm_dual_orthogonal_last b (hj ▸ hb)).symm
    · rw [N₀.ist_e a b hb, N₁.ist_e a b (hj ▸ hb)]
  have e'i : ∀ a (b : Fin r), N₀.j ≤ b.val → H.B (N₀.F'.e a) (N₀.ist b) = H.B (N₁.F'.e a) (N₁.ist b) := by
    intro a b hb
    by_cases ha : N₀.j ≤ a.val
    · rw [N₀.same a ha, N₁.same a (hj ▸ ha)]
      simp [ei a b hb, hc]
    have hl : a.val < r := lt_of_lt_of_le (not_le.1 ha) N₀.j_le
    exact (N₀.ist_e' ⟨a.val, hl⟩ b (not_le.1 ha) hb).trans
      (N₁.ist_e' ⟨a.val, hl⟩ b (hj ▸ not_le.1 ha) (hj ▸ hb)).symm
  have ww : ∀ p q : V × V, p.1 ∈ N₀.Wt → q.1 ∈ N₀.Wt → p.2 - p.1 ∈ N₀.F.X → q.2 - q.1 ∈ N₀.F.X → Cmp H p q := by
    intro p q hp hq hp' hq'
    have a1 := perp_X N₀.F (fun b => wt_e N₀ hq b.castSucc) _ hp'
    have a2 := B_swap0 H (perp_X N₀.F (fun b => wt_e N₀ hp b.castSucc) _ hq')
    have a3 := X_iso N₀.F hp' hq'
    simp only [map_sub, LinearMap.sub_apply] at a1 a2 a3
    unfold Cmp
    linear_combination -a1 - a2 - a3
  obtain ⟨s, hs, hS⟩ := exists_isometry (H := H)
    {p | (∃ a, p = (N₀.F.e a, N₁.F.e a)) ∨ (∃ a, p = (N₀.F'.e a, N₁.F'.e a)) ∨
      (∃ b : Fin r, N₀.j ≤ b.val ∧ p = (N₀.ist b, N₁.ist b)) ∨ (p.1 ∈ N₀.Wt ∧ p.2 ∈ N₁.Wt ∧ p.2 - p.1 ∈ N₀.F.X)}
    (by
      rintro p (⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨p0, p1, p2⟩) q (⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨q0, q1, q2⟩)
      · exact ee a b
      · exact ee' a b
      · exact ei a b hb
      · exact (wt_e N₀ q0 a).trans (wt_e N₁ q1 a).symm
      · exact Cmp.symm (ee' b a)
      · exact e'e' a b
      · exact e'i a b hb
      · exact (wt_e' N₀ q0 a).trans (wt_e' N₁ q1 a).symm
      · exact Cmp.symm (ei b a ha)
      · exact Cmp.symm (e'i b a ha)
      · exact (N₀.ist_iso a b ha hb).trans (N₁.ist_iso a b (hj ▸ ha) (hj ▸ hb)).symm
      · exact (wt_ist N₀ q0 a ha).trans (wt_ist N₁ q1 a (hj ▸ ha)).symm
      · exact Cmp.symm ((wt_e N₀ p0 b).trans (wt_e N₁ p1 b).symm)
      · exact Cmp.symm ((wt_e' N₀ p0 b).trans (wt_e' N₁ p1 b).symm)
      · exact Cmp.symm ((wt_ist N₀ p0 b hb).trans (wt_ist N₁ p1 b (hj ▸ hb)).symm)
      · exact ww p q p0 q0 p2 q2)
    (by
      refine eq_top N₀ _ (fun a => ⟨_, Submodule.subset_span (Or.inl ⟨a, rfl⟩), rfl⟩)
        (fun a => ⟨_, Submodule.subset_span (Or.inr (Or.inl ⟨a, rfl⟩)), rfl⟩)
        (fun b hb => ⟨_, Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨b, hb, rfl⟩))), rfl⟩) fun w hw => ?_
      obtain ⟨u, hu, hx⟩ := decomp N₁ (perp_transfer h (wt_e N₀ hw))
      exact ⟨(w, u), Submodule.subset_span (Or.inr (Or.inr (Or.inr ⟨hw, hu, hX ▸ hx⟩))), rfl⟩)
    (by
      refine eq_top N₁ _ (fun a => ⟨_, Submodule.subset_span (Or.inl ⟨a, rfl⟩), rfl⟩)
        (fun a => ⟨_, Submodule.subset_span (Or.inr (Or.inl ⟨a, rfl⟩)), rfl⟩)
        (fun b hb => ⟨_, Submodule.subset_span (Or.inr (Or.inr (Or.inl ⟨b, hj ▸ hb, rfl⟩))), rfl⟩) fun w hw => ?_
      obtain ⟨u, hu, hx⟩ := decomp N₀ (perp_transfer (AdaptInv.sameGr_symm h) (wt_e N₁ hw))
      exact ⟨(u, w), Submodule.subset_span (Or.inr (Or.inr (Or.inr ⟨hu, hw, by
        simpa using Submodule.neg_mem _ hx⟩))), rfl⟩)
  have se : ∀ a, s (N₀.F.e a) = N₁.F.e a := fun a => hS (_, _) (Or.inl ⟨a, rfl⟩)
  refine ⟨s, ⟨hs, s.bijective, fun a => ?_, fun y hy => ?_⟩,
    fun a => ⟨se a, hS (_, _) (Or.inr (Or.inl ⟨a, rfl⟩))⟩⟩
  · rw [LinearEquiv.coe_coe, se]
    exact h a.castSucc
  · let M : Submodule K V := N₀.F.X.comap ((s : V →ₗ[K] V) - LinearMap.id)
    have m1 : ∀ a, N₀.F.e a ∈ M := fun a => by
      change s (N₀.F.e a) - N₀.F.e a ∈ N₀.F.X
      rw [se]
      exact Xa_le_X _ _ (h a)
    have m2 : N₀.F.X ≤ M := Submodule.span_le.2 (by rintro _ ⟨b, -, rfl⟩; exact m1 _)
    have m3 : N₀.Wt ≤ M := fun w hw => by
      obtain ⟨u, hu, hx⟩ := decomp N₁ (perp_transfer h (wt_e N₀ hw))
      change s w - w ∈ N₀.F.X
      rw [show s w = u from hS (w, u) (Or.inr (Or.inr (Or.inr ⟨hw, hu, hX ▸ hx⟩))), ← hX]
      exact hx
    obtain ⟨u, hu, hx⟩ := decomp N₀ (w := y + star (H.B N₀.F.z y / N₀.F.T) • N₀.F.z) (fun a => by
      refine Fin.lastCases ?_ (fun a => ?_) a
      · have := N₀.F.hT
        change H.B N₀.F.z _ = 0
        simp only [map_add, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star, smul_eq_mul, pairing_lastVector_lastVector]
        field_simp
        ring
      · simp [hy a, pairing_isotropicSpan_lastVector N₀.F (e_mem_X _ a)])
    have m4 : y ∈ M := by
      have := M.sub_mem (M.sub_mem (m3 hu) (m2 hx))
        (M.smul_mem (star (H.B N₀.F.z y / N₀.F.T)) (m1 (Fin.last r)))
      simpa [FlagD.z] using this
    exact m4

end GlobalTheory.DegAsm.NFUnique

namespace GlobalTheory.DegAsm

theorem nf_unique : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F : FlagD H r) (N₀ N₁ : NF H r), SameGr F N₀.F → SameGr F N₁.F → N₀.j = N₁.j → N₀.c = N₁.c → N₀.T = N₁.T → pairM N₀.F N₀.F' N₀.j = pairM N₁.F N₁.F' N₁.j → ∃ s : V ≃ₗ[K] V, F.InN (s : V →ₗ[K] V) ∧ ∀ a, s (N₀.F.e a) = N₁.F.e a ∧ s (N₀.F'.e a) = N₁.F'.e a := by
  intro K V _ _ _ _ _ _ _ _ H _ r F N₀ N₁ h₀ h₁ hj hc hT hM
  have h : SameGr N₀.F N₁.F := fun a => by
    rw [AdaptInv.xa_eq h₀]
    simpa using Submodule.sub_mem _ (h₁ a) (h₀ a)
  obtain ⟨s, hs, he⟩ := NFUnique.main N₀ N₁ h hj hc hT hM
  exact ⟨s, AdaptInv.inN_of (AdaptInv.sameGr_symm h₀) _ hs, he⟩

end GlobalTheory.DegAsm
