import Formalism.WachLatticeTwists.HerrComplexInjectivity.GammaSubOneStatedForm
import Formalism.WachLatticeTwists.WachProductBases.WachConsequencesFurther

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JN

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N1 Formalism.RepresentationBoundsCohomology.N2

theorem gamma_sub_one_invariants_holds : GammaSubOneStatedForm := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB ι pr D _ _ _ _ W ρ κ _ b hs hP2 hρ hρN hb hγρ hcap x hxN hxinv
  have hX : S.X = S.π := by simp [HidaSetting.X, hs]
  have hγN : ∀ i, ∀ y ∈ W.N i, W.γ i y ∈ W.N i := by
    intro i y hy
    obtain ⟨y', hy', e⟩ := hP2 i y hy
    have : W.γ i y = y + S.X • y' := by rw [← e]; abel
    rw [this]
    exact (W.N i).add_mem hy ((W.N i).smul_mem _ hy')
  have key : ∀ i, ∃ x' : ↥(W.N i), (∀ d, ρ i d (x' : D) = x') ∧
      W.γ i (x i) - x i = IB.j B.X • (x' : D) := by
    intro i
    let ρN : Δ → ↥(W.N i) →+ ↥(W.N i) := fun d =>
      { toFun := fun y => ⟨ρ i d y, hρN i d y y.2⟩
        map_zero' := Subtype.ext (map_zero (ρ i d))
        map_add' := fun y z => Subtype.ext (map_add (ρ i d) _ _) }
    let γN : ↥(W.N i) →+ ↥(W.N i) :=
      { toFun := fun y => ⟨W.γ i y, hγN i y y.2⟩
        map_zero' := Subtype.ext (map_zero (W.γ i))
        map_add' := fun y z => Subtype.ext (map_add (W.γ i) _ _) }
    obtain ⟨x', hx'inv, hx'⟩ := gamma_sub_one_pi_invariants A Δ ↥(W.N i) κ (b i) ρN γN S.π (IB.j B.X)
      (fun d a y => Subtype.ext (hρ i d a y)) (fun d k => Subtype.ext (hb i d k))
      (fun d y => Subtype.ext (hγρ i d y))
      (fun y => by
        obtain ⟨y', hy', e⟩ := hP2 i y y.2
        exact ⟨⟨y', hy'⟩, Subtype.ext (by rw [← hX]; exact e)⟩)
      hcap ⟨x i, hxN i⟩ (fun d => Subtype.ext (hxinv i d))
    exact ⟨x', fun d => congrArg Subtype.val (hx'inv d), congrArg Subtype.val hx'⟩
  choose x' h1 h2 using key
  exact ⟨fun i => x' i, fun i => (x' i).2, h1, h2⟩

theorem delta_basis_holds : StatDeltaBasis := by
  intro O A _ _ _ S Δ _ _ _ ι pr D _ _ _ _ W ρ hR hu hΔ
  obtain ⟨hρ, -, -, htriv, κ, _, hb⟩ := hΔ
  have hρN : ∀ i d, ∀ x ∈ W.N i, ρ i d x ∈ W.N i := by
    intro i d x hx
    obtain ⟨x', hx', e⟩ := htriv i d x hx
    have : ρ i d x = x + S.π • x' := by rw [← e]; abel
    rw [this]
    exact (W.N i).add_mem hx ((W.N i).smul_mem _ hx')
  refine ⟨hρN, κ, inferInstance, ?_⟩
  have key : ∀ i, ∃ b' : Module.Basis κ A ↥(W.N i), ∀ d k, ρ i d (b' k : D) = (b' k : D) := by
    intro i
    let ρN : Δ → ↥(W.N i) →+ ↥(W.N i) := fun d =>
      { toFun := fun y => ⟨ρ i d y, hρN i d y y.2⟩
        map_zero' := Subtype.ext (map_zero (ρ i d))
        map_add' := fun y z => Subtype.ext (map_add (ρ i d) _ _) }
    obtain ⟨b', hb'⟩ := invariant_basis_average A Δ ↥(W.N i) κ (hb i).some ρN S.π
      (fun d d' x => Subtype.ext (by
        show ρ i (d * d') (x : D) = ρ i d (ρ i d' (x : D))
        rw [map_mul]; rfl))
      (fun x => Subtype.ext (by
        show ρ i 1 (x : D) = x
        rw [map_one]; rfl))
      (fun d a y => Subtype.ext (hρ i d a y)) hR hu
      (fun d x => by
        obtain ⟨x', hx', e⟩ := htriv i d x x.2
        exact ⟨⟨x', hx'⟩, Subtype.ext e⟩)
    exact ⟨b', fun d k => congrArg Subtype.val (hb' d k)⟩
  choose b' hb' using key
  exact ⟨b', hb'⟩

theorem invariants_exist_holds : StatInvExists := by
  intro O A A₀ _ _ _ _ _ S B Δ _ _ _ IB ι pr D _ _ _ _ W ρ hρ hφ hγ
  let T : Submodule O (ι → D) :=
    { carrier := {x | ∀ i d, ρ i d (x i) = x i}
      add_mem' := by
        intro a b ha hb i d
        rw [Pi.add_apply, map_add, ha, hb]
      zero_mem' := by
        intro i d
        rw [Pi.zero_apply, map_zero]
      smul_mem' := by
        intro c x hx i d
        rw [Pi.smul_apply, map_smul, hx] }
  have hinv : ∀ (a : A₀) (d : Δ), d • IB.j a = IB.j a := fun a => (IB.j_range _).2 ⟨a, rfl⟩
  let sm : A₀ → ↥T → ↥T := fun a x => ⟨fun i => IB.j a • x.1 i, fun i d => by
    show ρ i d (IB.j a • x.1 i) = _
    rw [hρ, hinv, x.2 i d]⟩
  letI : Module A₀ ↥T :=
    { smul := sm
      one_smul := fun x => Subtype.ext (funext fun i => by
        show IB.j 1 • x.1 i = x.1 i
        rw [map_one, one_smul])
      mul_smul := fun a b x => Subtype.ext (funext fun i => by
        show IB.j (a * b) • x.1 i = IB.j a • IB.j b • x.1 i
        rw [map_mul, mul_smul])
      smul_zero := fun a => Subtype.ext (funext fun i => by
        show IB.j a • (0 : D) = 0
        rw [smul_zero])
      smul_add := fun a x y => Subtype.ext (funext fun i => by
        show IB.j a • (x.1 i + y.1 i) = IB.j a • x.1 i + IB.j a • y.1 i
        rw [smul_add])
      add_smul := fun a b x => Subtype.ext (funext fun i => by
        show IB.j (a + b) • x.1 i = IB.j a • x.1 i + IB.j b • x.1 i
        rw [map_add, add_smul])
      zero_smul := fun x => Subtype.ext (funext fun i => by
        show IB.j 0 • x.1 i = 0
        rw [map_zero, zero_smul]) }
  haveI : IsScalarTower O A₀ ↥T := ⟨fun o a x => Subtype.ext (funext fun i => by
    show IB.j (o • a) • x.1 i = o • (IB.j a • x.1 i)
    rw [map_smul, smul_assoc])⟩
  let φ' : ↥T →ₗ[O] ↥T :=
    { toFun := fun x => ⟨fun i => W.φ i (x.1 (pr i)), fun i d => by
        show ρ i d (W.φ i (x.1 (pr i))) = _
        rw [← hφ, x.2]⟩
      map_add' := fun x y => Subtype.ext (funext fun i => map_add (W.φ i) _ _)
      map_smul' := fun c x => Subtype.ext (funext fun i => map_smul (W.φ i) _ _) }
  let γ' : ↥T →ₗ[O] ↥T :=
    { toFun := fun x => ⟨fun i => W.γ i (x.1 i), fun i d => by
        show ρ i d (W.γ i (x.1 i)) = _
        rw [← hγ, x.2]⟩
      map_add' := fun x y => Subtype.ext (funext fun i => map_add (W.γ i) _ _)
      map_smul' := fun c x => Subtype.ext (funext fun i => map_smul (W.γ i) _ _) }
  exact ⟨↥T, inferInstance, inferInstance, inferInstance, inferInstance, T.subtype, φ', γ',
    Subtype.val_injective, fun _ _ _ => rfl,
    fun x => ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨x', rfl⟩; exact x'.2⟩,
    fun _ _ => rfl, fun _ _ => rfl, hρ⟩

end Formalism.RepresentationBoundsCohomology.JN
