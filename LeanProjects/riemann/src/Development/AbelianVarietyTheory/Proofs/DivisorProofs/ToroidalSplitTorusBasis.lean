import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatMatTransposeMulGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthLetters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixResult
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.HalfGeo
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfGeo

set_option maxHeartbeats 800000 in
theorem gram_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)
    (K : Type) [Field K] [CharZero K] (ξ₀ : Sp K ⟶ Xo.XF c) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) →
    SplitK Z.t (ξ₀ ≫ Z.j) q → ∀ (N : ℕ) (b : Module.Basis (Fin N) ℤ Dw.La),
    ∃ (s : Fin N → (Over.mk ξ₀ ⟶ Z.oF.t.G)) (ζ : Kˣ), IsPrimitiveRoot ζ q ∧ IsGram Z.oF.t q s ζ (GlobalTheory.EqHalf.gram Dw b) ∧
      (∀ a : Over.mk ξ₀ ⟶ Z.oF.t.G, a ^ q = 1 → ∃ n : Fin N → ℕ, a = ∏ m, s m ^ n m) ∧
      (∀ (α : 𝓞 E) (m : Fin N), s m ≫ Z.oF.t.act.act α = ∏ m', s m' ^ GlobalTheory.EqHalf.latMat Dw b α m' m) := by
  intro E _ _ _ H Dw l Xo c O _ β Z K _ _ ξ₀ q hq hζ hsplit N b
  obtain ⟨ζ₀, hζ₀⟩ := hζ
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq
  haveI : NeZero q := ⟨hq⟩
  let Ω := AlgebraicClosure K
  let io : K →+* Ω := algebraMap K Ω
  haveI := epi_spMap_field io
  let x : Sp Ω ⟶ Xo.XF c := spMap io ≫ ξ₀
  obtain ⟨-, I, -⟩ := Z.oF.geom Ω x (Spec.preimage (x ≫ pullback.fst _ _ ≫ Xo.s)).hom (Spec.map_preimage _).symm
  have hev : ∀ a, I.ev q a ^ q = 1 := fun a => (I.onto q hq0 _).2 ⟨a, rfl⟩
  have hd : ∀ m, ∃ s : Over.mk ξ₀ ⟶ Z.oF.t.G, spMap io ≫ s.left = (I.ev q (b m)).left := fun m =>
    gram_descend Z.oF.t.G Z.t.G Z.j Z.m.φ Z.m.cart io ξ₀ q (hsplit Ω io) _ (hev _)
  choose s hs using hd
  let hKo : Over.mk x ⟶ Over.mk ξ₀ := Over.homMk (spMap io) rfl
  have hKl : hKo.left = spMap io := rfl
  have hinj : ∀ a a' : Over.mk ξ₀ ⟶ Z.oF.t.G, hKo ≫ a = hKo ≫ a' → a = a' := by
    intro a a' e
    ext1
    have := congrArg (fun u => u.left) e
    exact (cancel_epi (spMap io)).1 this
  have hs' : ∀ m, hKo ≫ s m = I.ev q (b m) := fun m => by ext1; exact hs m
  have hst : ∀ m, s m ^ q = 1 := fun m => hinj _ _ (by rw [MonObj.comp_pow, hs', hev, MonObj.comp_one])
  have hp1 : IsPrimitiveRoot (io ζ₀) q := hζ₀.map_of_injective io.injective
  have hp2 : IsPrimitiveRoot (I.ζ q : Ω) q := (I.ζ_prim q hq0).map_of_injective (f := Units.coeHom Ω) Units.val_injective
  obtain ⟨i, -, hi⟩ := hp1.eq_pow_of_pow_eq_one hp2.pow_eq_one
  have hne : ζ₀ ^ i ≠ 0 := pow_ne_zero _ (hζ₀.ne_zero hq)
  let ζ : Kˣ := Units.mk0 _ hne
  have hmap : Units.map (io : K →* Ω) ζ = I.ζ q := by
    ext
    simp [ζ, ← hi]
  have hminj : Function.Injective (Units.map (io : K →* Ω)) := Units.map_injective io.injective
  refine ⟨s, ζ, ?_, ⟨hst, fun m m' => ?_⟩, ?_, ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective (f := Units.map (io : K →* Ω)) (by rw [hmap]; exact I.ζ_prim q hq0) hminj
  · let P := GlobalTheory.Obj.toPolAV Z.oF
    obtain ⟨cq, hcq, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P q (s m) (s m') (hst m) (hst m')
    obtain ⟨u, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 cq
    have hN := (GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk ξ₀)).2 (Over.mk x) hKo (s m) (s m') (unitOn u) hcq
    rw [hKl, GlobalTheory.Ex.Specialise.map_unitOn] at hN
    have hI := I.isom q hq0 (b m) (b m')
    rw [← hs', ← hs'] at hI
    have t : ∀ m, (hKo ≫ s m) ^ q = 1 := fun m => by rw [hs', hev]
    have e1 := (GlobalTheory.LevelCompare.weil_existsUnique P q (hKo ≫ s m) (hKo ≫ s m') (t m) (t m')).unique hN hI
    have e2 := GlobalTheory.Ex.Specialise.unitOn_bijective.1 e1
    rw [← hmap, ← map_zpow] at e2
    have e3 := hminj e2
    rw [e3] at hcq
    exact hcq
  · intro a ha
    obtain ⟨y, hy⟩ := (I.onto q hq0 (hKo ≫ a)).1 (by rw [← MonObj.comp_pow, ha, MonObj.comp_one])
    let ev : Multiplicative Dw.La →* (Over.mk x ⟶ Z.oF.t.G) :=
      MonoidHom.mk' (fun u => I.ev q u.toAdd) (fun u v => I.add q _ _)
    let pb : (Over.mk ξ₀ ⟶ Z.oF.t.G) →* (Over.mk x ⟶ Z.oF.t.G) :=
      MonoidHom.mk' (fun u => hKo ≫ u) (fun u v => MonObj.comp_mul _ _ _)
    refine ⟨fun m => (b.repr y m % q).toNat, hinj _ _ ?_⟩
    have e1 : hKo ≫ a = ev (Multiplicative.ofAdd (∑ m, b.repr y m • b m)) := by
      rw [b.sum_repr, ← hy]; rfl
    rw [e1, ofAdd_sum, map_prod]
    change _ = pb _
    rw [map_prod]
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [ofAdd_zsmul, map_zpow, map_pow]
    change I.ev q (b m) ^ _ = (hKo ≫ s m) ^ _
    rw [hs', ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hq))]
    exact zpow_eq_zpow_emod' _ (hev _)
  · intro α m
    let ev : Multiplicative Dw.La →* (Over.mk x ⟶ Z.oF.t.G) :=
      MonoidHom.mk' (fun u => I.ev q u.toAdd) (fun u v => I.add q _ _)
    let pb : (Over.mk ξ₀ ⟶ Z.oF.t.G) →* (Over.mk x ⟶ Z.oF.t.G) :=
      MonoidHom.mk' (fun u => hKo ≫ u) (fun u v => MonObj.comp_mul _ _ _)
    apply hinj
    have e1 : hKo ≫ s m ≫ Z.oF.t.act.act α = ev (Multiplicative.ofAdd (∑ m', b.repr (α • b m) m' • b m')) := by
      rw [b.sum_repr, ← Category.assoc, hs']
      exact (I.lin q α (b m)).symm
    rw [e1, ofAdd_sum, map_prod]
    change _ = pb _
    rw [map_prod]
    refine Finset.prod_congr rfl fun m' _ => ?_
    rw [ofAdd_zsmul, map_zpow, map_zpow, GlobalTheory.EqHalf.latMat_apply]
    change I.ev q (b m') ^ _ = (hKo ≫ s m') ^ _
    rw [hs']

end GlobalTheory.HalfGeo
