import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHarrisTaylorDatumAtPrimeCoprimeStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPel.HT.Gen.CxSmooth

theorem of_geomFibres {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] (g : ℕ)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Y), SmoothOfRelativeDimension g (pullback.snd f t)) :
    SmoothOfRelativeDimension g f := by
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  have key : ∀ x, n x = g := by
    intro x
    let κ := Y.residueField (f x)
    let k := AlgebraicClosure κ
    let t : Sp k ⟶ Y := spMap (algebraMap κ k) ≫ Y.fromSpecResidueField (f x)
    have ht : f x = t (IsLocalRing.closedPoint k) := by
      show f x = (Y.fromSpecResidueField (f x)) ((spMap (algebraMap κ k)) (IsLocalRing.closedPoint k))
      rw [Scheme.fromSpecResidueField_apply]
    obtain ⟨z, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := t) x (IsLocalRing.closedPoint k) ht
    have sq := IsPullback.paste_vert (isPullback_morphismRestrict (pullback.fst f t) (W x))
      (IsPullback.of_hasPullback f t)
    have h₁ : SmoothOfRelativeDimension (n x) (((pullback.fst f t) ⁻¹ᵁ W x).ι ≫ pullback.snd f t) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback sq (hd x)
    have h₂ : SmoothOfRelativeDimension g (((pullback.fst f t) ⁻¹ᵁ W x).ι ≫ pullback.snd f t) :=
      IsZariskiLocalAtSource.comp (h k t) _
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h₁ h₂ ⟨z, show pullback.fst f t z ∈ W x by rw [hz.1]; exact hW x⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← key x]; exact hd x

def baseOfG {p : ℕ} [Fact p.Prime] {D : Datum p} (gb : GBase D.toG ℂ) : Base D ℂ where
  unit k hk := by
    refine Ne.isUnit (Nat.cast_ne_zero.2 ?_)
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hk)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    have h1 : IsUnit ((p : ℂ)) := Ne.isUnit (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    have h2 := h1.map β
    rw [map_natCast, CharP.cast_eq_zero] at h2
    exact not_isUnit_zero h2

theorem genericModel_complex_smooth {p : ℕ} [Fact p.Prime] (D : Datum p) (gb : GBase D.toG ℂ) (N : ℕ) (hN : 3 ≤ N)
    (hNp : N.Coprime p) (X : GenModel gb N) : ∃ d, SmoothOfRelativeDimension d X.s := by
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D ℂ (baseOfG gb) N hN hNp
  obtain ⟨j, hj, -, hjs, -⟩ := GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre p D ℂ (baseOfG gb) ℂ (RingHom.id ℂ) gb rfl
    (fun i => (RingHom.id_comp _).symm) N hN hNp M X
  have h1 : SmoothOfRelativeDimension (D.a * (D.n - 1)) (pullback.snd M.s (spMap (RingHom.id ℂ))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) M.smooth
  have : IsOpenImmersion j := hj
  have h0 : SmoothOfRelativeDimension 0 j := inferInstance
  refine ⟨0 + D.a * (D.n - 1), ?_⟩
  rw [← hjs]
  infer_instance

theorem card_torsion_of_gTateIso (G : GDatum) {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    Nat.card {q : Q // q ^ ℓ = 1} = ℓ ^ Module.finrank ℤ G.La := by
  haveI := G.freeLa
  haveI := G.finLa
  haveI : NeZero ℓ := ⟨hℓ.ne'⟩
  set r := Module.finrank ℤ G.La
  let B := Module.finBasis ℤ G.La
  let v : (Fin r → ZMod ℓ) → G.La := fun c => ∑ i, ((c i).val : ℤ) • B i
  have evneg : ∀ x y : G.La, I.ev ℓ (x - y) = I.ev ℓ x * (I.ev ℓ y)⁻¹ := fun x y => by
    rw [eq_mul_inv_iff_mul_eq, ← I.add, sub_add_cancel]
  have hrep : ∀ c i, B.repr (v c) i = ((c i).val : ℤ) := fun c i => by
    simp [v, Module.Basis.repr_self, Finsupp.single_apply]
  let F : (Fin r → ZMod ℓ) → {q : Q // q ^ ℓ = 1} := fun c => ⟨I.ev ℓ (v c), (I.onto ℓ hℓ _).2 ⟨_, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro c c' hcc
      have h1 : I.ev ℓ (v c - v c') = 1 := by
        rw [evneg, mul_inv_eq_one]; exact congrArg Subtype.val hcc
      obtain ⟨y, hy⟩ := (I.ker ℓ hℓ _).1 h1
      funext i
      have h2 := congrArg (fun z => B.repr z i) hy
      simp only [map_sub, Finsupp.sub_apply, hrep, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at h2
      have h3 := congrArg (fun z : ℤ => (z : ZMod ℓ)) h2
      simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul,
        ZMod.natCast_self, zero_mul] at h3
      exact sub_eq_zero.1 h3
    · rintro ⟨q, hq⟩
      obtain ⟨x, rfl⟩ := (I.onto ℓ hℓ q).1 hq
      let c : Fin r → ZMod ℓ := fun i => (B.repr x i : ZMod ℓ)
      have hdiv : ∀ i, (ℓ : ℤ) ∣ ((c i).val : ℤ) - B.repr x i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp [c]
      choose y hy using hdiv
      refine ⟨c, Subtype.ext ?_⟩
      show I.ev ℓ (v c) = I.ev ℓ x
      have e1 : v c = x + ℓ • ∑ i, y i • B i := by
        refine B.ext_elem fun i => ?_
        rw [hrep, map_add, map_nsmul, Finsupp.add_apply, Finsupp.smul_apply, map_sum]
        simp only [map_zsmul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
          Finsupp.single_apply, smul_eq_mul, nsmul_eq_mul]
        simp only [mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        linear_combination hy i
      rw [e1, I.add, (I.ker ℓ hℓ _).2 ⟨_, rfl⟩, _root_.mul_one]
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem relDim_A {G : GDatum} (gb : GBase G ℂ) (N : ℕ) (X : GenModel gb N) :
    SmoothOfRelativeDimension (G.m * G.n * Module.finrank ℚ G.F / 2) X.univ.A.hom := by
  have hab := X.univ.ab
  have : Smooth X.univ.A.hom := hab.smooth
  have : IsProper X.univ.A.hom := hab.proper
  have : GeometricallyConnected X.univ.A.hom := hab.geomConnected
  refine of_geomFibres X.univ.A.hom _ fun k _ _ t => ?_
  let B := (Over.pullback t).obj X.univ.A
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := by show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have : Smooth B.hom := hB.smooth
  have : GeometricallyConnected B.hom := hB.geomConnected
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton (f := B.hom)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected B.hom (Classical.arbitrary _)
  suffices e : d = G.m * G.n * Module.finrank ℚ G.F / 2 by rw [← e]; exact hd
  obtain ⟨β, hβ⟩ := Spec.map_surjective (t ≫ X.s)
  obtain ⟨I, -⟩ := X.univ.geom k t β.hom hβ.symm
  have h2k : ((2 : ℕ) : k) ≠ 0 := by
    have h : IsUnit ((2 : ℕ) : ℂ) := Ne.isUnit (by norm_num)
    have := h.map β.hom
    rw [map_natCast] at this
    exact this.ne_zero
  have c₁ := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B d 2 hB hd h2k
  have c₂ := card_torsion_of_gTateIso G I (ℓ := 2) two_pos
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback X.univ.A t) (𝟙 _) t
    (Category.id_comp t).symm
  have c₃ : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ 2 = 1} =
      Nat.card {q : Over.mk t ⟶ X.univ.A // q ^ 2 = 1} :=
    Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
      show x ^ 2 = 1 ↔ e x ^ 2 = 1
      rw [← map_pow, MulEquiv.map_eq_one_iff])
  rw [c₁, c₂, G.rankLa] at c₃
  have := Nat.pow_right_injective le_rfl c₃
  omega

theorem genModel_smooth : ∀ (G : GDatum) (gb : GBase G ℂ) (N : ℕ), 3 ≤ N → ∀ X : GenModel gb N,
    (∃ d : ℕ, SmoothOfRelativeDimension d X.s) ∧
      SmoothOfRelativeDimension (G.m * G.n * Module.finrank ℚ G.F / 2) X.univ.A.hom := by
  intro G gb N hN X
  refine ⟨?_, relDim_A gb N X⟩
  obtain ⟨p, _, D, hNp, rfl⟩ := GlobalTheory.T.exists_harrisTaylorDatum_at_prime_coprime G N (by omega)
  exact genericModel_complex_smooth D gb N hN hNp X

end GlobalTheory.UPel.HT.Gen.CxSmooth
