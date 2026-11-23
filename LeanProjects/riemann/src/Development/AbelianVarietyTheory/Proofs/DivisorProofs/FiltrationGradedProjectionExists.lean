import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismOfCompatibleFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)
open scoped Classical

namespace GlobalTheory.GrFiltProj

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}

theorem eq_of_germ_eq {F : X.Modules} {n : ℕ} {U W : X.Opens} {e : Fin n → Γ(F, U)} (he : IsFrame e) (h : W ≤ U)
    (s t : Γ(F, W)) (H : ∀ hW : genericPoint X ∈ W, F.presheaf.germ W _ hW s = F.presheaf.germ W _ hW t) : s = t := by
  refine (he.basis h).repr.injective (Finsupp.ext fun i => ?_)
  by_cases hW : genericPoint X ∈ W
  · refine germ_injective_of_isIntegral X _ hW ?_
    rw [← TriFrame.FlagOf.stalkBasis_repr_germ he h, ← TriFrame.FlagOf.stalkBasis_repr_germ he h, H hW]
  · obtain rfl : W = ⊥ := by
      by_contra hne
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
      exact hW (genericPoint_mem hx)
    exact Subsingleton.elim _ _

def img {V : X.Opens} (f' : ∀ a, Fin (r a) → Γ(E' a, V)) (b : ι) (z : Σ a, Fin (r a)) : Γ(E' b, V) :=
  if h : z.1 = b then f' b (Fin.cast (congrArg r h) z.2) else 0

def stalkProj {V : X.Opens} (f' : ∀ a, Fin (r a) → Γ(E' a, V)) {c : (Σ a, Fin (r a)) → Γ(L, V)} (hc : IsFrame c)
    (b : ι) (x : X) (hx : x ∈ V) : L.presheaf.stalk x →ₗ[X.presheaf.stalk x] (E' b).presheaf.stalk x :=
  (hc.stalkBasis x hx).constr (X.presheaf.stalk x) fun z => (E' b).presheaf.germ V x hx (img f' b z)

omit [IsIntegral X] in
theorem stalkProj_frame {V : X.Opens} (f' : ∀ a, Fin (r a) → Γ(E' a, V)) {c : (Σ a, Fin (r a)) → Γ(L, V)}
    (hc : IsFrame c) (b : ι) (x : X) (hx : x ∈ V) (z : Σ a, Fin (r a)) :
    stalkProj f' hc b x hx (L.presheaf.germ V x hx (c z)) = (E' b).presheaf.germ V x hx (img f' b z) := by
  rw [← hc.stalkBasis_apply x hx, stalkProj, Module.Basis.constr_basis]

omit [IsIntegral X] in
theorem stalkProj_germ {V : X.Opens} (f' : ∀ a, Fin (r a) → Γ(E' a, V)) {c : (Σ a, Fin (r a)) → Γ(L, V)}
    (hc : IsFrame c) (b : ι) (x : X) (hx : x ∈ V) (s : Γ(L, V)) :
    stalkProj f' hc b x hx (L.presheaf.germ V x hx s) =
      (E' b).presheaf.germ V x hx (∑ j, (hc.basis le_rfl).repr s ⟨b, j⟩ • f' b j) := by
  conv_lhs => rw [← (hc.basis le_rfl).sum_repr s]
  simp only [map_sum, QCoh.germ_smul, map_smul, hc.basis_apply, resM_self, stalkProj_frame]
  rw [Fintype.sum_sigma, Finset.sum_eq_single b]
  · simp [img]
  · intro a _ ha
    simp [img, ha]
  · simp

theorem stalkProj_comp_self {o : ι → ℕ} {T : ∀ a, E a ⟶ L} {u : ∀ a, E a ⟶ E' a} {V : X.Opens}
    {f : ∀ a, Fin (r a) → Γ(E a, V)} (hf : ∀ a, IsFrame (f a)) {f' : ∀ a, Fin (r a) → Γ(E' a, V)}
    {hf' : ∀ a, IsFrame (f' a)} {c : (Σ a, Fin (r a)) → Γ(L, V)} {hc : IsFrame c}
    (hA : AdaptedAt o T u f f' hf' c hc) (b : ι) (x : X) (hx : x ∈ V) :
    stalkProj f' hc b x hx ∘ₗ QCoh.stalkLinear (T b) x = QCoh.stalkLinear (u b) x := by
  refine ((hf b).stalkBasis x hx).ext fun i => ?_
  rw [LinearMap.comp_apply, IsFrame.stalkBasis_apply, QCoh.stalkLinear_germ, QCoh.stalkLinear_germ, stalkProj_germ]
  congr 1
  conv_rhs => rw [← ((hf' b).basis le_rfl).sum_repr ((u b).app V (f b i))]
  simp only [(hA b i).2, IsFrame.basis_apply, resM_self]

theorem stalkProj_comp_lt {o : ι → ℕ} {T : ∀ a, E a ⟶ L} {u : ∀ a, E a ⟶ E' a} {V : X.Opens}
    {f : ∀ a, Fin (r a) → Γ(E a, V)} (hf : ∀ a, IsFrame (f a)) {f' : ∀ a, Fin (r a) → Γ(E' a, V)}
    {hf' : ∀ a, IsFrame (f' a)} {c : (Σ a, Fin (r a)) → Γ(L, V)} {hc : IsFrame c}
    (hA : AdaptedAt o T u f f' hf' c hc) {a b : ι} (hab : o a < o b) (x : X) (hx : x ∈ V) :
    stalkProj f' hc b x hx ∘ₗ QCoh.stalkLinear (T a) x = 0 := by
  refine ((hf a).stalkBasis x hx).ext fun i => ?_
  rw [LinearMap.comp_apply, IsFrame.stalkBasis_apply, QCoh.stalkLinear_germ, stalkProj_germ]
  have (j : Fin (r b)) := (hA a i).1 ⟨b, j⟩ hab
  simp [this]

theorem stalkProj_eq {o : ι → ℕ} (ho : Function.Injective o) {T : ∀ a, E a ⟶ L} {u : ∀ a, E a ⟶ E' a}
    {V V₁ : X.Opens}
    {f : ∀ a, Fin (r a) → Γ(E a, V)} (hf : ∀ a, IsFrame (f a)) {f' : ∀ a, Fin (r a) → Γ(E' a, V)}
    {hf' : ∀ a, IsFrame (f' a)} {c : (Σ a, Fin (r a)) → Γ(L, V)} {hc : IsFrame c}
    (hA : AdaptedAt o T u f f' hf' c hc)
    {f₁ : ∀ a, Fin (r a) → Γ(E a, V₁)} (hf₁ : ∀ a, IsFrame (f₁ a)) {f₁' : ∀ a, Fin (r a) → Γ(E' a, V₁)}
    {hf₁' : ∀ a, IsFrame (f₁' a)} {c₁ : (Σ a, Fin (r a)) → Γ(L, V₁)} {hc₁ : IsFrame c₁}
    (hA₁ : AdaptedAt o T u f₁ f₁' hf₁' c₁ hc₁) (b : ι) (hV : genericPoint X ∈ V) (hV₁ : genericPoint X ∈ V₁)
    {v : genStalk L} (hv : v ∈ genSpan o T (o b + 1)) :
    stalkProj f' hc b _ hV v = stalkProj f₁' hc₁ b _ hV₁ v := by
  refine LinearMap.eqOn_span ?_ hv
  rintro _ ⟨a, ha, W, hW, s, rfl⟩
  rw [← QCoh.stalkLinear_germ]
  rcases (Nat.lt_succ_iff.1 ha).lt_or_eq with h | h
  · exact (LinearMap.congr_fun (stalkProj_comp_lt hf hA h _ hV) _).trans
      (LinearMap.congr_fun (stalkProj_comp_lt hf₁ hA₁ h _ hV₁) _).symm
  · obtain rfl := ho h
    exact (LinearMap.congr_fun (stalkProj_comp_self hf hA a _ hV) _).trans
      (LinearMap.congr_fun (stalkProj_comp_self hf₁ hA₁ a _ hV₁) _).symm

theorem exists_isProj : ∀ {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}
    (o : ι → ℕ), Function.Injective o → ∀ (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a), (∀ a, Mono (u a)) →
    (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ LocAdapted r o T u V) → FrameMem r o T u → GenSpanEq r o T u →
    ∀ b, ∃ κ : (filtSub o T (o b + 1)).toMod ⟶ E' b, IsProj r o T u b κ := by
  intro X _ ι _ L E E' r o ho T u _ hcov hmem _ b
  let D : Type := {d : Σ V : X.Opens, (∀ a, Fin (r a) → Γ(E a, V)) × (∀ a, Fin (r a) → Γ(E' a, V)) ×
      ((Σ a, Fin (r a)) → Γ(L, V)) // (∀ a, IsFrame (d.2.1 a)) ∧
        ∃ (hf' : ∀ a, IsFrame (d.2.2.1 a)) (hc : IsFrame d.2.2.2), AdaptedAt o T u d.2.1 d.2.2.1 hf' d.2.2.2 hc}
  have hf (d : D) := d.2.1
  have hf' (d : D) := d.2.2.1
  have hc (d : D) := d.2.2.2.1
  have hA (d : D) : AdaptedAt o T u d.1.2.1 d.1.2.2.1 (hf' d) d.1.2.2.2 (hc d) := d.2.2.2.2
  let Q : (Σ a, Fin (r a)) → Prop := fun z => o z.1 < o b + 1
  have ex (d : D) := exists_isFrame_subP (filtSub o T (o b + 1)) d.1.2.2.2 (hc d) Q fun V' h a => by
    simpa only [Q, not_lt] using hmem (o b + 1) _ _ (hf d) _ (hf' d) _ (hc d) (hA d) V' h a
  choose t ht htc using ex
  let σ := (Fintype.equivFin {z // Q z}).symm
  obtain ⟨κ, hκ⟩ := FrameGlue.exists_hom_of_frames X (filtSub o T (o b + 1)).toMod (E' b) _ D (fun d => d.1.1)
    (fun x => by
      obtain ⟨V, hx, f, hf, f', hf', c, hc, hA⟩ := hcov x
      exact ⟨⟨⟨V, f, f', c⟩, hf, hf', hc, hA⟩, hx⟩)
    (fun d => t d ∘ σ) (fun d => (ht d).comp_equiv σ) (fun d a => img d.1.2.2.1 b (σ a)) (fun i j a => by
      refine eq_of_germ_eq (hf' i b) inf_le_left _ _ fun hW => ?_
      have e1 := (((ht i).comp_equiv σ).basis (inf_le_left : i.1.1 ⊓ j.1.1 ≤ i.1.1)).sum_repr
        (resM _ inf_le_right ((t j ∘ σ) a))
      have e2 := congrArg (fun s => stalkProj i.1.2.2.1 (hc i) b _ hW.1
        (L.presheaf.germ _ _ hW ((filtSub o T (o b + 1)).incl.app _ s))) e1
      simp only [map_sum, Scheme.Modules.Hom.app_smul, IsFrame.basis_apply, app_resM, Function.comp_apply, htc,
        QCoh.germ_smul, germ_resM, map_smul, stalkProj_frame] at e2
      have hm : L.presheaf.germ _ _ hW.2 (j.1.2.2.2 (σ a)) ∈ genSpan o T (o b + 1) := by
        rw [← htc]
        exact (filtSub o T (o b + 1)).incl_app_mem _ hW.2
      rw [stalkProj_eq ho (hf i) (hA i) (hf j) (hA j) b hW.1 hW.2 hm, stalkProj_frame] at e2
      simp only [map_sum, QCoh.germ_smul, germ_resM]
      exact e2.symm)
  refine ⟨κ, fun V f hf f' hf' c hc hA z s hs => ?_⟩
  let d : D := ⟨⟨V, f, f', c⟩, hf, hf', hc, hA⟩
  by_cases hz : Q z
  · obtain rfl : s = t d ⟨z, hz⟩ := (filtSub o T (o b + 1)).incl_app_injective V (hs.trans (htc d ⟨z, hz⟩).symm)
    have := hκ d (σ.symm ⟨z, hz⟩)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
    exact this
  · have h1 := (hmem (o b + 1) V f hf f' hf' c hc hA V le_rfl (Pi.single z 1)).1 (by
      have := (filtSub o T (o b + 1)).incl_app_mem s
      rw [hs] at this
      simpa [Pi.single_apply, resM_self] using this) z (Nat.le_of_not_lt hz)
    rw [Pi.single_eq_same] at h1
    have : Subsingleton Γ(X, V) := subsingleton_of_zero_eq_one h1.symm
    exact (Module.subsingleton Γ(X, V) Γ(E' b, V)).elim _ _

end GlobalTheory.GrFiltProj

end
