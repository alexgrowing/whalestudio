import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleSurjectionFactorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegQuotTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parIndMap_surjective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {V W : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (Levi k m) V}
    {ρ' : Representation ℂ (Levi k m) W} (f : ρ.IntertwiningMap ρ') (hρ : IsSmooth ρ)
    (hf : Function.Surjective f) : Function.Surjective (parIndMap e f) := by
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let σ₀ : Representation ℂ (parab k e) V := (twist ρ (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
    hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
    (isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont)
    (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
  intro x _
  refine Submodule.subset_span ⟨(), -x, ?_⟩
  show x = (0 : _) - -x
  simp

theorem prod₂_map_surjective {r t : ℕ} {U U' W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (hσ : IsSmooth σ) (hρ : IsSmooth ρ) (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ' ρ'), Function.Surjective F := by
  have hσ' : IsSmooth σ' := (IsSubquotient.of_surjective f hf).isSmooth hσ
  have hc : Continuous fun h : Levi k (Two (Fin r) (Fin t)) => (h false, h true) :=
    (continuous_apply false).prodMk (continuous_apply true)
  have h1 : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) := LinearMap.rTensor_surjective W hf
  have h2 : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight σ' g) := LinearMap.lTensor_surjective U' hg
  have h1' : Function.Surjective (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := h1
  have h2' : Function.Surjective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ' g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := h2
  have s1 := parIndMap_surjective (two (stdSum (rfl : r + t = r + t))) _
    (isSmooth_comp (isSmooth_extTensor hσ hρ) _ hc) h1'
  have s2 := parIndMap_surjective (two (stdSum (rfl : r + t = r + t))) _
    (isSmooth_comp (isSmooth_extTensor hσ' hρ) _ hc) h2'
  exact ⟨(parIndMap (two (stdSum (rfl : r + t = r + t))) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ' g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)).comp (parIndMap (two (stdSum (rfl : r + t = r + t)))
      (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)), s2.comp s1⟩

theorem nonempty_prodIrr_equiv_of_cast {c c' N : ℕ} (h : c = c') (x : Fin c → IrrGL k) (x' : Fin c' → IrrGL k)
    (hx : ∀ i, x i = x' (Fin.cast h i)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x' a).1 = N) :
    Nonempty ((prodIrr x hd).Equiv (prodIrr x' hd')) := by
  subst h
  obtain rfl : x = x' := funext fun i => by simpa using hx i
  exact ⟨.refl _⟩

theorem append_term (Δ : Segment k) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len)
    (hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len)
    (i : Fin ((segLow Δ a h0).len + (segHigh Δ a h1).len)) :
    Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i = Δ.term (Fin.cast hlen i) := by
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    rfl
  | right j =>
    rw [Fin.append_right]
    show (Δ.first.nu ((a : ℕ) : ℂ)).nu ((j : ℕ) : ℂ) = Δ.first.nu (((segLow Δ a h0).len + (j : ℕ) : ℕ) : ℂ)
    rw [IrrGL.nu_nu]
    show _ = Δ.first.nu ((a + (j : ℕ) : ℕ) : ℂ)
    push_cast
    rfl

theorem hasFiniteLength_prodIrr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) :=
  GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ (isSmooth_piTensor fun a => (x a).2.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem nontrivial_prodIrr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k)
    (hd : ∑ a, (x a).1 = N) : Nontrivial (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) :=
  GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp _ (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x)
    (isSmooth_piTensor fun a => (x a).2.rep.smooth)

theorem exists_surjective_of_equiv {G A B C D : Type} [Group G] [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] {α : Representation ℂ G A}
    {β : Representation ℂ G B} {γ : Representation ℂ G C} {δ : Representation ℂ G D} (E : Nonempty (β.Equiv α))
    (F : ∃ f : β.IntertwiningMap γ, Function.Surjective f) (H : Nonempty (γ.Equiv δ)) :
    ∃ f : α.IntertwiningMap δ, Function.Surjective f := by
  obtain ⟨E⟩ := E
  obtain ⟨F, hF⟩ := F
  obtain ⟨H⟩ := H
  exact ⟨H.toIntertwiningMap.comp (F.comp E.symm.toIntertwiningMap),
    H.toLinearEquiv.surjective.comp (hF.comp E.symm.toLinearEquiv.surjective)⟩

theorem exists_surjective_of_prod₂_equiv {r t : ℕ} {U U' W W' A D : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [AddCommGroup A]
    [Module ℂ A] [AddCommGroup D] [Module ℂ D] {σ : Representation ℂ (GL (Fin r) k) U}
    {σ' : Representation ℂ (GL (Fin r) k) U'} {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} {α : Representation ℂ (GL (Fin (r + t)) k) A}
    {δ : Representation ℂ (GL (Fin (r + t)) k) D} (hσ : IsSmooth σ) (hρ : IsSmooth ρ) (f : σ.IntertwiningMap σ')
    (g : ρ.IntertwiningMap ρ') (hf : Function.Surjective f) (hg : Function.Surjective g)
    (E : Nonempty ((prod₂ σ ρ).Equiv α)) (H : Nonempty ((prod₂ σ' ρ').Equiv δ)) :
    ∃ F : α.IntertwiningMap δ, Function.Surjective F :=
  exists_surjective_of_equiv E (prod₂_map_surjective hσ hρ f g hf hg) H

theorem exists_surjective_append {p q : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (u v : IrrGL k)
    (hx : ∑ a, (x a).1 = u.1) (hy : ∑ a, (y a).1 = v.1) (h : ∑ a, (Fin.append x y a).1 = u.1 + v.1)
    (hd : ∑ i, (![u, v] i).1 = u.1 + v.1)
    (fu : (prodIrr x hx).IntertwiningMap u.rep) (hfu : Function.Surjective fu)
    (fv : (prodIrr y hy).IntertwiningMap v.rep) (hfv : Function.Surjective fv) :
    ∃ F : (prodIrr (Fin.append x y) h).IntertwiningMap (prodIrr ![u, v] hd), Function.Surjective F :=
  exists_surjective_of_prod₂_equiv (isSmooth_prodIrr x hx) (isSmooth_prodIrr y hy) fu fv hfu hfv
    (GlobalTheory.T.product_irreducible_append_equiv k p q u.1 v.1 x y hx hy h) (nonempty_prod₂_equiv_prodIrr_pair u v hd)

theorem quotient_of_quotient {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V) (Q : Representation ℂ G X)
    (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (hf : ∃ f : P.IntertwiningMap Q, Function.Surjective f)
    (hQ : Nontrivial X) : ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  obtain ⟨f, hf⟩ := hf
  exact GlobalTheory.T.cosocle_surjection_factor σ P Q hc hfl f hf hQ

theorem quottwo : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : IsLSeg Δ π) (a : ℕ) (h0 : 0 < a) (h1 : a < Δ.len) (u v : IrrGL k)
    (hu : IsLSeg (segLow Δ a h0) u.rep) (hv : IsLSeg (segHigh Δ a h1) v.rep) (hd : ∑ i, (![u, v] i).1 = N),
    ∃ f : (prodIrr ![u, v] hd).IntertwiningMap π, Function.Surjective f := by
  intro k _ _ _ _ hA Δ N V _ _ π hπ a h0 h1 u v hu hv hd
  have hN : u.1 + v.1 = N := hd.symm ▸ (Fin.sum_univ_two (fun i => (![u, v] i).1)).symm
  subst hN
  obtain ⟨hx, -, fu, hfu, -⟩ := hu
  obtain ⟨hy, -, fv, hfv, -⟩ := hv
  obtain ⟨hΔ, hc⟩ := hπ
  have hlen : (segLow Δ a h0).len + (segHigh Δ a h1).len = Δ.len := by
    show a + (Δ.len - a) = Δ.len
    omega
  have hsum : ∑ i, (Fin.append (segLow Δ a h0).term (segHigh Δ a h1).term i).1 = u.1 + v.1 := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    exact congrArg₂ (· + ·) hx hy
  exact quotient_of_quotient π _ _ hc (hasFiniteLength_prodIrr hA _ hΔ)
    (exists_surjective_of_equiv (nonempty_prodIrr_equiv_of_cast hlen _ Δ.term (append_term Δ a h0 h1 hlen) hsum hΔ)
      (exists_surjective_append _ _ u v hx hy hsum hd fu hfu fv hfv) ⟨.refl _⟩) (nontrivial_prodIrr hA _ hd)

end GlobalTheory.CompanionTheory.SegQuotTwo

end
