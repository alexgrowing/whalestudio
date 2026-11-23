import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelTorsionWeilPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.CubPair

theorem exists_lift {R K : Type} [CommRing R] [Field K] [Algebra R K] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {G₀ : Over (Sp K)} [GrpObj G₀] [IsCommMonObj G₀] {F : G₀.left ⟶ G.left}
    (h : IsGrpPullback G₀ G (spMap (algebraMap R K)) F) {N : ℕ} (x : Tors G N K) :
    ∃ x₀ : Tors G₀ N K, x.1.left = x₀.1.left ≫ F := by
  let f : Sp K ⟶ Sp R := spMap (algebraMap R K)
  let T : Over (Sp K) := SpAlg K K
  have hc : T.hom ≫ f = (SpAlg R K).hom := by
    show spMap (algebraMap K K) ≫ spMap (algebraMap R K) = spMap (algebraMap R K)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let ρ : SpAlg R K ⟶ Over.mk (T.hom ≫ f) := Over.homMk (𝟙 _) ((Category.id_comp _).trans hc)
  let Φ : (T ⟶ G₀) →* (SpAlg R K ⟶ G) := (preHom ρ).comp (pushHom h T)
  have hΦ : ∀ x, (Φ x).left = x.left ≫ F := fun x => Category.id_comp _
  have hi : Function.Injective Φ := fun x y e =>
    Over.OverMorphism.ext (h.1.hom_ext (by rw [← hΦ, ← hΦ, e]) ((Over.w x).trans (Over.w y).symm))
  let a : T ⟶ G₀ := Over.homMk (h.1.lift x.1.left T.hom ((Over.w x.1).trans hc.symm)) (h.1.lift_snd _ _ _)
  have ha : Φ a = x.1 := Over.OverMorphism.ext ((hΦ _).trans (h.1.lift_fst _ _ _))
  exact ⟨⟨a, hi (by rw [map_pow, ha, x.2, map_one])⟩, (h.1.lift_fst _ _ _).symm⟩

theorem cubWeil_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t : SAB H S}
    {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : ℕ} (T : Over S') (s : T.left ⟶ S) (hs : s = T.hom ≫ f)
    {x y : T ⟶ t'.G} (hx₀ : x ^ k = 1) (hy₀ : y ^ k = 1) {x₁ y₁ : Over.mk s ⟶ t.G} (hx : x₁.left = x.left ≫ m.φ)
    (hy : y₁.left = y.left ≫ m.φ) {z : Γ(T.left, ⊤)ˣ} (h : GlobalTheory.UU.CubWeil t.cub k x₁ y₁ z) :
    GlobalTheory.UU.CubWeil t'.cub k x y z := by
  subst hs
  obtain rfl : x₁ = Out.toBase m.cart.1.w x := Over.OverMorphism.ext hx
  obtain rfl : y₁ = Out.toBase m.cart.1.w y := Over.OverMorphism.ext hy
  obtain ⟨z', hz', -⟩ := GlobalTheory.UU.existsUnique_cubWeil t'.cub hx₀ hy₀
  have h' := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f t.G t'.G m.cm m.cart.1.w
    (fun T a b => Over.OverMorphism.ext (m.cart.2 T a b _ _ rfl rfl).symm) _ _ _ _ m.lin k T x y z' hz'
  obtain rfl : z = z' := h.unique h'
  exact hz'

theorem cubWeil_eq_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (t : SAB H (Sp R)) (t₀ : SAB H (Sp K)) (mK : SABMap t₀ t (spMap (algebraMap R K))) (GG₀ : PDivGroup p K) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀) (ε₀ : (PDivGroup.mu p K).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsOfType Dw t₀ → IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ → ∀ (GG : PDivGroup p R) (θ : TorsionMap t.G GG) (e : GG₀ ≅ GG.baseChange K), IsModel K θ → GenCompat mK.φ θ θ₀ e → ∀ (n : ℕ) (x x' : Tors t.G (p ^ n) K) (ζ : Kˣ) (s s' : GG.A n →ₐ[R] R), θ.pt n K x = (Algebra.ofId R K).comp s → θ.pt n K x' = (Algebra.ofId R K).comp s' → GlobalTheory.UU.CubWeil t.cub (p ^ n) x.1 x'.1 (unitOn ζ) → (ζ : K) = Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp s') (fun _ _ => .all _ _) ((e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom).app n ((1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R (GG.A n)))) := by
  intro E _ _ _ H Dw p _ R K _ _ _ _ _ _ _ _ t t₀ mK GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hT hP GG θ e _ hG n x x' ζ s s' hs hs' hc
  have hpp : p.Prime := Fact.out
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  obtain ⟨x₀, hx⟩ := exists_lift mK.cart x
  obtain ⟨x₀', hx'⟩ := exists_lift mK.cart x'
  obtain ⟨y, hy⟩ := hP.onto n K hp (θ₀.pt n K x₀')
  have hb : (spMap (algebraMap R K) : (SpAlg K K).left ⟶ Sp R) = (SpAlg K K).hom ≫ spMap (algebraMap R K) := by
    show spMap (algebraMap R K) = spMap (algebraMap K K) ≫ spMap (algebraMap R K)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hc₀ : GlobalTheory.UU.CubWeil t₀.cub (p ^ n) x₀.1 x₀'.1 (unitOn ζ) :=
    cubWeil_pull mK (SpAlg K K) _ hb x₀.2 x₀'.2 hx hx' hc
  have key := cubWeil_eq_polPairing E H Dw p K t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hT hP n x₀ x₀' y ζ hy.symm hc₀
  have he : ∀ b, e.hom.app n (e.inv.app n b) = b := fun b =>
    congrArg (fun f : GG₀ ⟶ GG₀ => f.app n b) e.hom_inv_id
  have ext : ∀ (z : Tors t.G (p ^ n) K) (z₀ : Tors t₀.G (p ^ n) K) (r : GG.A n →ₐ[R] R), z.1.left = z₀.1.left ≫ mK.φ →
      θ.pt n K z = (Algebra.ofId R K).comp r → ∀ w : K ⊗[R] GG.A n,
      Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp r) (fun _ _ => .all _ _) w =
        θ₀.pt n K z₀ (e.hom.app n w) := fun z z₀ r hz hr w => by
    induction w using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans ((congrArg _ (map_zero (e.hom.app n))).trans (map_zero _)).symm
    | add a b ha hb =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ha hb).trans
        ((congrArg _ (map_add (e.hom.app n) a b)).trans (map_add _ _ _)).symm)
    | tmul c a =>
      have h1 : (c ⊗ₜ[R] a : K ⊗[R] GG.A n) = c • ((1 : K) ⊗ₜ[R] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      have h2 : θ₀.pt n K z₀ (e.hom.app n (c ⊗ₜ[R] a : K ⊗[R] GG.A n)) = c • θ₀.pt n K z₀ (e.hom.app n ((1 : K) ⊗ₜ[R] a)) :=
        (congrArg (fun w : K ⊗[R] GG.A n => θ₀.pt n K z₀ (e.hom.app n w)) h1).trans
          ((congrArg _ (map_smul (e.hom.app n) c _)).trans (map_smul _ c _))
      rw [h2, ← hG n K z z₀ hz a, hr, Algebra.TensorProduct.lift_tmul, smul_eq_mul]
      rfl
  have bc : ∀ w : K ⊗[R] GG.A n, CartierDual.baseChange R K (GG.A n)
      ((1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R (GG.A n))) w =
      Algebra.TensorProduct.lift (AlgHom.id K K) ((Algebra.ofId R K).comp s) (fun _ _ => .all _ _) w := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul c a =>
      rw [CartierDual.baseChange_tmul_tmul, Algebra.TensorProduct.lift_tmul, _root_.one_mul, Algebra.smul_def, mul_comm]
      rfl
  let φ₀ : CartierDual K (GG₀.A n) := toConv (θ₀.pt n K x₀).toLinearMap
  have hφ : CartierDual.map (e.inv.app n) (CartierDual.baseChange R K (GG.A n)
      ((1 : K) ⊗ₜ[R] (toConv s.toLinearMap : CartierDual R (GG.A n)))) = φ₀ := CartierDual.ext_apply fun b =>
    (bc (e.inv.app n b)).trans ((ext x x₀ s hx hs _).trans (congrArg (θ₀.pt n K x₀) (he b)))
  refine key.trans (Eq.trans ?_ (ext x' x₀' s' hx' hs' _).symm)
  refine (apply_charElem _ n φ₀).trans ?_
  refine Eq.trans ?_ (congrArg (θ₀.pt n K x₀') (he _)).symm
  rw [← hy]
  exact congrArg (fun φ => (τ₀ y).pt n (pol₀.hom.app n φ)) hφ.symm

end GlobalTheory.GroupBplus.Aff.CubPair
