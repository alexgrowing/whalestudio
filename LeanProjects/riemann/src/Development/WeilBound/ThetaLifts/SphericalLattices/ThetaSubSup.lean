import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locrep

noncomputable section

namespace PositivityTheory.Sph

open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

section Core

variable {V H : Type} [AddCommGroup V] [Module ℂ V]

def Stab (S A : Submodule ℂ V) (U : Set H) (T : H → Module.End ℂ V) (P : Submodule ℂ V) : Prop :=
  A ≤ P ∧ P ≤ S ∧ ∀ h ∈ U, ∀ x ∈ P, T h x ∈ P

variable {S A : Submodule ℂ V} {U : Set H} {T : H → Module.End ℂ V}

theorem Stab.sup {P P' : Submodule ℂ V} (h : Stab S A U T P) (h' : Stab S A U T P') : Stab S A U T (P ⊔ P') := by
  refine ⟨le_sup_of_le_left h.1, sup_le h.2.1 h'.2.1, fun i hi x hx => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem_sup (h.2.2 i hi y hy) (h'.2.2 i hi z hz)

theorem Stab.not_mem {s : V} (hgen : ∀ φ ∈ S, φ ∈ A ⊔ Submodule.span ℂ {z | ∃ h ∈ U, z = T h s}) {P : Submodule ℂ V}
    (h : Stab S A U T P) (hP : P ≠ S) : s ∉ P := by
  intro hs
  refine hP (le_antisymm h.2.1 fun φ hφ => (sup_le h.1 (Submodule.span_le.2 ?_)) (hgen φ hφ))
  rintro _ ⟨i, hi, rfl⟩
  exact h.2.2 i hi s hs

theorem Stab.sup_ne {s : V} (hs : s ∈ S) (hgen : ∀ φ ∈ S, φ ∈ A ⊔ Submodule.span ℂ {z | ∃ h ∈ U, z = T h s})
    (hline : ∀ φ ∈ S, ∃ (m : ℕ) (k : Fin (m + 1) → H) (w : Fin (m + 1) → ℂ) (c : ℂ),
      (∀ i, k i ∈ U ∧ w i • T (k i) s = s) ∧ ∑ i, w i • T (k i) φ - c • s ∈ A)
    {P P' : Submodule ℂ V} (h : Stab S A U T P) (h' : Stab S A U T P') (hP : P ≠ S) (hP' : P' ≠ S) : P ⊔ P' ≠ S := by
  intro e
  have hs' : s ∈ P ⊔ P' := e ▸ hs
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hs'
  obtain ⟨m, k, w, c, hw, hc⟩ := hline x (h.2.1 hx)
  have hxP : ∑ i, w i • T (k i) x ∈ P := P.sum_mem fun i _ => P.smul_mem _ (h.2.2 _ (hw i).1 x hx)
  have hyP : ∑ i, w i • T (k i) y ∈ P' := P'.sum_mem fun i _ => P'.smul_mem _ (h'.2.2 _ (hw i).1 y hy)
  have hsum : ∑ i, w i • T (k i) x + ∑ i, w i • T (k i) y = ((m + 1 : ℕ) : ℂ) • s := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← smul_add, ← map_add, hxy, (hw _).2]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have h1 : c • s ∈ P := by
    have := P.sub_mem hxP (h.1 hc)
    rwa [sub_sub_cancel] at this
  have h2 : (((m + 1 : ℕ) : ℂ) - c) • s ∈ P' := by
    have e2 : (((m + 1 : ℕ) : ℂ) - c) • s = ∑ i, w i • T (k i) y + (∑ i, w i • T (k i) x - c • s) := by
      rw [sub_smul, ← hsum]; abel
    rw [e2]
    exact P'.add_mem hyP (h'.1 hc)
  by_cases hc0 : c = 0
  · subst hc0
    refine Stab.not_mem hgen h' hP' ?_
    have := P'.smul_mem (((m + 1 : ℕ) : ℂ))⁻¹ h2
    rwa [sub_zero, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m), one_smul] at this
  · refine Stab.not_mem hgen h hP ?_
    have := P.smul_mem c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

end Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

omit [NumberField E] in
theorem one_uat (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by simp [mat]

theorem stab_of (L : IsLocRep M ψ om v ω ρ) {N} (hN : GlobalTheory.Published.ThetaSub om v N) :
    Stab (SB _) (augAt om v) (UAt σ W (evFin F v)) (fun h => ω (1, h)) N :=
  ⟨hN.1, hN.2.1, fun h hh x hx => hN.2.2 h hh x hx _ (L.pres 1 (one_uat v) h hh x (hN.2.1 hx))
    ((L.acts 1 (one_uat v) h hh x (hN.2.1 hx) _).2 rfl)⟩

theorem thetaSub_of (L : IsLocRep M ψ om v ω ρ) {N}
    (hN : Stab (SB _) (augAt om v) (UAt σ W (evFin F v)) (fun h => ω (1, h)) N) : GlobalTheory.Published.ThetaSub om v N :=
  ⟨hN.1, hN.2.1, fun h hh φ hφ φ₁ _ hA => by
    rw [(L.acts 1 (one_uat v) h hh φ (hN.2.1 hφ) φ₁).1 hA]
    exact hN.2.2 h hh φ hφ⟩

theorem thetaSub_sup (L : IsLocRep M ψ om v ω ρ) {N N'} (hN : GlobalTheory.Published.ThetaSub om v N)
    (hN' : GlobalTheory.Published.ThetaSub om v N') : GlobalTheory.Published.ThetaSub om v (N ⊔ N') :=
  thetaSub_of L ((stab_of L hN).sup (stab_of L hN'))

theorem sup_ne_of (L : IsLocRep M ψ om v ω ρ) (hs : SphAt M ψ om v ∨ IrrAt om v) {N N'} (hN : GlobalTheory.Published.ThetaSub om v N)
    (hN' : GlobalTheory.Published.ThetaSub om v N') (h1 : N ≠ SB _) (h2 : N' ≠ SB _) : N ⊔ N' ≠ SB _ := by
  rcases hs with hs | hs
  · obtain ⟨s, hs⟩ := hs ω ρ L
    exact Stab.sup_ne hs.mem hs.gen hs.line (stab_of L hN) (stab_of L hN') h1 h2
  · have e1 := (hs N hN).resolve_right h1
    have e2 := (hs N' hN').resolve_right h2
    rw [e1, e2, sup_idem]
    rw [e1] at h1
    exact h1

theorem maxAt_of (L : IsLocRep M ψ om v ω ρ) (hs : SphAt M ψ om v ∨ IrrAt om v) : PositivityTheory.HoweDualityUnitaryAlt.MaxAt om v := by
  intro N N' hN hN'
  have hq : GlobalTheory.Published.ThetaSub om v (N ⊔ N') ∧ N ⊔ N' ≠ SB _ :=
    ⟨thetaSub_sup L hN.prop.1 hN'.prop.1, sup_ne_of L hs hN.prop.1 hN'.prop.1 hN.prop.2 hN'.prop.2⟩
  exact (hN.eq_of_ge hq le_sup_left).symm.trans (hN'.eq_of_ge hq le_sup_right)

theorem locRep_tri {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Y : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G Y om om') (v : Pl F) :
    (∃ ω ρ, IsLocRep G.M B.ψ om v ω ρ) ∧ ∃ ω ρ, IsLocRep G.M' B.ψ om' v ω ρ :=
  ⟨PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B G.V G.W G.M om
      ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, ⟨_, _, hT.weil⟩⟩ v,
    PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B G.V' G.W G.M' om'
      ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', ⟨_, _, hT.weil'⟩⟩ v⟩

theorem maxFinT_of (h : SphTri) : PositivityTheory.HoweDualityUnitaryAlt.MaxFinT := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _
  obtain ⟨h1, h2⟩ := h F E σ B a a' G X om om' hT v
  obtain ⟨⟨ω, ρ, L⟩, ⟨ω', ρ', L'⟩⟩ := locRep_tri hT v
  exact ⟨maxAt_of L h1, maxAt_of L' h2⟩

end PositivityTheory.Sph

end
