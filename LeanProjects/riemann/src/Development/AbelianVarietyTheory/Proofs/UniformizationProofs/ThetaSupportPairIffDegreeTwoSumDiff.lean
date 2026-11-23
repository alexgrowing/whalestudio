import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TensorComponentNeZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpacesStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorAbelianPartNeZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorFullLeftSupportStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamilyStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIffStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU.SuppRel

theorem component_ne_zero_iff_mod_two (F : Type) [Field F] (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (E : Type) [AddCommGroup E] [Module F E] (W : X → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module F (W a)] (ex : ∀ a, E →ₗ[F] W a)
    (hsep : ∀ s, (∀ a, ex a s = 0) → s = 0)
    (hcut : ∀ (α : X) (s : E), ∃ s' : E, ∀ β,
      ((∃ mu, β = α + 2 • mu) → ex β s' = ex β s) ∧ ((¬ ∃ mu, β = α + 2 • mu) → ex β s' = 0))
    (hinj : ∀ α, ex α ≠ 0 → ∀ s, (∀ β, (¬ ∃ mu, β = α + 2 • mu) → ex β s = 0) → ex α s = 0 → s = 0)
    (w : TensorProduct F E E)
    (hfull : ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E →ₗ[F] E) w = 0 → π = 0)
    (hoff : ∀ α β, (¬ ∃ a b, α = a + b ∧ β = a - b) → TensorProduct.map (ex α) (ex β) w = 0)
    (a b : X) :
    TensorProduct.map (ex (a + b)) (ex (a - b)) w ≠ 0 ↔ ex (a + b) ≠ 0 ∧ ex (a - b) ≠ 0 := by
  let H : AddSubgroup X := (nsmulAddMonoidHom 2 : X →+ X).range
  have hfg : AddGroup.FG X := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hH : H.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X two_ne_zero
  have hfin : Finite (X ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  have hcl : ∀ α β : X, (QuotientAddGroup.mk β : X ⧸ H) = QuotientAddGroup.mk α ↔ ∃ mu, β = α + 2 • mu := by
    intro α β
    rw [eq_comm, QuotientAddGroup.eq]
    constructor
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply] at h; rw [h]; abel⟩
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply, h]; abel⟩
  refine GlobalTheory.tensor_component_ne_zero_iff F X (X ⧸ H) QuotientAddGroup.mk E W ex hsep ?_ ?_ w hfull ?_ _ _ ?_
  · intro c s
    obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨s', hs'⟩ := hcut α s
    exact ⟨s', fun β => ⟨fun h => (hs' β).1 ((hcl α β).1 h), fun h => (hs' β).2 fun h' => h ((hcl α β).2 h')⟩⟩
  · intro α hα s hs h0
    exact hinj α hα s (fun β hβ => hs β fun h => hβ ((hcl α β).1 h)) h0
  · intro α β h
    refine hoff α β ?_
    rintro ⟨x, y, rfl, rfl⟩
    exact h ((hcl _ _).2 ⟨y, by rw [two_nsmul]; abel⟩)
  · exact (hcl _ _).2 ⟨b, by rw [two_nsmul]; abel⟩

theorem supp_rel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ a b : D.X, ((∃ j, (f a).f j ≠ 0) ∧ ∃ j, (f b).f j ≠ 0) ↔ (U.Supp (Kbar V) 2 (a + b) ∧ U.Supp (Kbar V) 2 (a - b))) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ a b
  obtain ⟨hG, hB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hG θ
  obtain ⟨s₀, hs₀, -⟩ := hB f
  obtain ⟨r, n, t, t', s, s', hr, hexp, hA, hAB⟩ := GlobalTheory.T.additionFormula_algClosure_with_expansions hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨hth0, -, -⟩ := GlobalTheory.T.expF_of_theta_degree_one hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨ex, hex, huniq, hsep, hsupp⟩ := GlobalTheory.T.exists_linear_fourierJacobi_expansion_family hL hL2 V hV D A G U (Kbar V) 2 (by norm_num)
  obtain ⟨hcut, -, hinj⟩ := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces hL hL2 V hV D A G U 2 (by norm_num)
  obtain ⟨hon, hoff⟩ := GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff V D (Kbar V) s₀ r n s s' hr hAB
  have hcV : CharZero V := hV.2.2
  have hchar : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  have h2 : (2 : Kbar V) ≠ 0 := two_ne_zero
  let u : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t i)
  let u' : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t' i)
  have hfull := GlobalTheory.T.additionTensor_full_left_support hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) h2 (SecMod.mk _ th) n u u' hA
    (fun h => by
      obtain ⟨j, hj⟩ := hth0
      exact hj ((SecMod.eq_zero_iff _).1 h j))
  have hmap : ∀ α β : D.X, TensorProduct.map (ex α) (ex β) (∑ i, TensorProduct.tmul (Kbar V) (u i) (u' i)) =
      ∑ i, TensorProduct.tmul (Kbar V) (SecMod.mk _ (s i α) : WB D (Kbar V) 2 α)
        (SecMod.mk _ (s' i β) : WB D (Kbar V) 2 β) := by
    intro α β
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.map_tmul, huniq _ _ (hexp i).1 α, huniq _ _ (hexp i).2 β]
    rfl
  have key := component_ne_zero_iff_mod_two (Kbar V) D.X (EA A (jFK (R := V) (Kbar V)) 2)
    (fun α => WB D (Kbar V) 2 α) ex hsep ?_ ?_ _ hfull (fun α β h => (hmap α β).trans (hoff α β h)) a b
  · rw [hsupp, hsupp, ← key, hmap, hon, GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ a,
      GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ b]
  · intro α v
    obtain ⟨v', p, hp, hβ⟩ := hcut α _ _ (hex v)
    refine ⟨SecMod.mk _ v', fun β => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rcases hβ β with h' | h'
      · exact (huniq _ _ hp β).symm.trans h'.2
      · exact absurd h h'.1
    · rcases hβ β with h' | h'
      · exact absurd h'.1 h
      · refine (SecMod.eq_zero_iff _).2 fun j => ?_
        rw [← huniq _ _ hp β]
        exact h'.2 j
  · intro α hα v hv h0
    exact (SecMod.eq_zero_iff _).2 (hinj α ((hsupp α).2 hα) _ _ (hex v)
      (fun β hβ => (SecMod.eq_zero_iff _).1 (hv β hβ)) ((SecMod.eq_zero_iff _).1 h0))

end GlobalTheory.UU.SuppRel
