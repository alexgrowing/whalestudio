import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtPtOfCharacter
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusTorsionToAbelianTorsionThetaActionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorPointZeroOfPowerEigenStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSectionsIrreducibleThetaGroup
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineZeroConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPowersExpansionSupportSubgroupStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.PrimeIndex

theorem exists_injective_character (F : Type) [Field F] [IsAlgClosed F] (l : ℕ) (hl : (l : F) ≠ 0) :
    ∃ φ : Multiplicative (ZMod l) →* Fˣ, Function.Injective φ := by
  have : NeZero (l : F) := ⟨hl⟩
  have : NeZero l := NeZero.of_neZero_natCast F
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F l
  have hu : IsPrimitiveRoot (hζ.isUnit (NeZero.ne l)).unit l := hζ.isUnit_unit (NeZero.ne l)
  exact ⟨(Subgroup.subtype _).comp (AddEquiv.toMultiplicativeLeft hu.zmodEquivZPowers).toMonoidHom,
    Subtype.val_injective.comp (AddEquiv.toMultiplicativeLeft hu.zmodEquivZPowers).injective⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem sval_pow_of_pullG (U : PreU I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (θ : U.SecGT T 1) (σ : U.SecGT T k)
    (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := R) F))) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)))
    (h₁ : U.PullG F φ 1 θ th) (hk : U.PullG F φ k σ t)
    (hp : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ k)
    (z : (TFK (R := R) F ⊗ A.A).left) (JA) (hA : Good A.L z JA) :
    sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t (𝟙 _) z JA =
      sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => ((1 : ℕ) : ℤ)) th
        (𝟙 _) z JA ^ k := by
  let y₀ : (TFK (R := R) F ⊗ A.A).left ⟶ ((Over.pullback (jK R)).obj G).left :=
    (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left
  have ih : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id]; rfl
  have ha : y₀ ≫ U.gen.hom.left = (snd (TFK (R := R) F) A.A).left :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ih).trans (Category.comp_id _))
  have hcomm : ((fst (TFK (R := R) F) A.A).left ≫ φ.left) ≫ T.hom = (y₀ ≫ pullback.fst G.hom (jK R)) ≫ G.hom := by
    have e₁ : φ.left ≫ T.hom = jFK (R := R) F ≫ jK R := Over.w φ
    have e₂ : U.gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w U.gen.inv
    have e₃ : (fst (TFK (R := R) F) A.A).left ≫ jFK (R := R) F = (snd (TFK (R := R) F) A.A).left ≫ A.A.hom :=
      (Over.w (fst (TFK (R := R) F) A.A)).trans (Over.w (snd (TFK (R := R) F) A.A)).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ jK R) e₃).trans ?_)))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (y₀ ≫ ·) pullback.condition)).symm
    rw [← e₂]
    simp only [y₀, Category.assoc]
  let h : (TFK (R := R) F ⊗ A.A).left ⟶ (T ⊗ G).left := pullback.lift _ _ hcomm
  have h₃ : h ≫ (fst T G).left = (fst (TFK (R := R) F) A.A).left ≫ φ.left := pullback.lift_fst _ _ _
  have h₂ : h ≫ (snd T G).left = y₀ ≫ pullback.fst G.hom (jK R) := pullback.lift_snd _ _ _
  obtain ⟨JG, hG⟩ := exists_good_pt U.P.L.isLB z
  have e₁ : 𝟙 _ ≫ (snd (TFK (R := R) F) A.A).left = y₀ ≫ U.gen.hom.left := (Category.id_comp _).trans ha.symm
  have e₃ : h ≫ (fst T G).left = 𝟙 _ ≫ (fst (TFK (R := R) F) A.A).left ≫ φ.left := h₃.trans (Category.id_comp _).symm
  have a := h₁ _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG
  have b := (hk _ (𝟙 _) y₀ h e₁ h₂ e₃ z JA JG hA hG).trans ((hp _ h z JG hG).trans (congrArg (· ^ k) a.symm))
  rw [pow_one, mul_pow, ← Units.val_pow_eq_pow_val] at b
  exact (Units.mul_right_inj _).1 b

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem hom_zmod_eq_zero_of_support : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (l : ℕ), l.Prime → ∀ g : D.X →+ ZMod l, (∀ α, (∃ j, (f α).f j ≠ 0) → g α = 0) → g = 0) := by
  intro L₁ L₂ V _ _ _ hV D A G _ _ U θ f hθ l hl g hg
  have := hV.1
  have := hV.2.2
  have : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  have hl0 : (l : Kbar V) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hl1 : 1 ≤ l := hl.one_le
  obtain ⟨φ, hφ⟩ := exists_injective_character (Kbar V) l hl0
  let χ₀ : Multiplicative D.X →* (Kbar V)ˣ := φ.comp (AddMonoidHom.toMultiplicative g)
  have hχ : ∀ α, χ₀ (Multiplicative.ofAdd α) = φ (Multiplicative.ofAdd (g α)) := fun _ => rfl
  have hχl : χ₀ ^ l = 1 := MonoidHom.ext fun α => by
    show χ₀ (Multiplicative.ofAdd α.toAdd) ^ l = 1
    rw [hχ, ← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero, map_one]
  suffices H : χ₀ = 1 by
    refine AddMonoidHom.ext fun α => ?_
    have e : φ (Multiplicative.ofAdd (g α)) = φ 1 := by rw [← hχ, H, map_one]; rfl
    exact congrArg Multiplicative.toAdd (hφ e)
  obtain ⟨p, pb, pv, pt, pz⟩ := exists_gtPt_of_character V D (Kbar V) χ₀
  obtain ⟨o, -, -, ot, oz⟩ := exists_gtPt_of_character V D (Kbar V) 1
  obtain ⟨m, minj, macts, madd⟩ := GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action L₁ L₂ V hV D A G U l hl1
  let P : {g : GtPtF D (Kbar V) // GtTors D l g} := ⟨p, pt l hχl⟩
  let O : {g : GtPtF D (Kbar V) // GtTors D l g} := ⟨o, ot l (one_pow l)⟩
  have ho : o = 0 := (TorusExt.isZero_iff_eq o).1 (oz.2 rfl)
  have mO : m O = 1 := by
    have := madd O O O ((TorusExt.isAdd_iff_eq o o o).2 (by rw [ho, add_zero]))
    exact left_eq_mul.1 this
  suffices H : m P = 1 by
    have e : p = o := congrArg Subtype.val (minj (H.trans mO.symm))
    exact pz.1 (e ▸ oz.2 rfl)
  obtain ⟨σ, fl, hσ, hfl, hpow⟩ := GlobalTheory.T.thetaPowers_expansion_support_subgroup L₁ L₂ V hV D A G U g.ker θ f hθ.1 (fun α hα j => by
    by_contra hj
    exact hα (hg α ⟨j, hj⟩)) l hl1
  obtain ⟨th, hth, -⟩ := PullSec.existsUnique_pullG U (Kbar V) (toUnit _) 1 θ
  obtain ⟨s₀, hs₀, -⟩ := PullSec.existsUnique_pullB D (Kbar V) (toUnit _) 1 f
  obtain ⟨t, ht, -⟩ := PullSec.existsUnique_pullG U (Kbar V) (toUnit _) l σ
  obtain ⟨s, hs, -⟩ := PullSec.existsUnique_pullB D (Kbar V) (toUnit _) l fl
  obtain ⟨⟨j₀, hj₀⟩, -, -⟩ := GlobalTheory.T.expF_of_theta_degree_one L₁ L₂ V hV D A G U θ f hθ th s₀ hth hs₀
  have hts := GlobalTheory.expF_of_pull V D _ A G U (Kbar V) l σ fl t s hσ ht hs
  obtain ⟨ex, ex₁, ex₂, ex₃, -⟩ := GlobalTheory.UU.ExpLinMap.exists_expansion_linear L₁ L₂ V hV D A G U (Kbar V) l hl1
  obtain ⟨hpl, hacts⟩ := macts P
  obtain ⟨ϑ, hϑ⟩ := (GlobalTheory.ThetaIrred.main L₁ L₂ _ A (Kbar V) (jFK (R := V) (Kbar V)) l hl0).1 (m P) hpl
  obtain ⟨w, hw, hΦ⟩ := hacts ϑ hϑ
  obtain ⟨t', ht'⟩ := ThetaScalar.exists_actVal A.isLB ϑ t
  have hact := ht'.isActOf A.isLB
  obtain ⟨c, hc⟩ := GlobalTheory.UU.phiRaw_torus V D (Kbar V) l p w pb hw
  have hs' := hc s _ (hΦ t t' s _ hts (ex₁ (SecMod.mk _ t')) hact) (fun α hα z J hJ => by
    obtain ⟨j, hj⟩ := (GlobalTheory.pullB_ne_zero_iff V D (Kbar V) l fl s hs α).1 hα
    have hm : g α = 0 := by
      by_contra h0
      exact hj (hfl α h0 j)
    refine Units.ext ((pv α z J hJ).trans ?_)
    have e₁ : scal (𝟙 (Spec (CommRingCat.of (Kbar V)))) ((1 : (Kbar V)ˣ) : Kbar V) = 1 := by simp [scal]
    rw [hχ, hm, ofAdd_zero, map_one, e₁]
    exact (gs_eq _ z ⊤ trivial _).trans ((congrArg _ (map_one _)).trans (map_one _)))
  have e : SecMod.mk _ t' = c.val • (SecMod.mk _ t : EA A (jFK (R := V) (Kbar V)) l) := by
    refine sub_eq_zero.1 (ex₃ _ fun α => ?_)
    rw [map_sub, map_smul, sub_eq_zero]
    refine SecMod.ext_coord fun j => (hs' α j).trans ?_
    rw [ex₂ t s hts α]
    rfl
  refine hϑ.symm.trans (GlobalTheory.T.thetaOperator_point_zero_of_power_eigen _ A (Kbar V) (jFK (R := V) (Kbar V)) l hl1 (SecMod.mk _ th) (SecMod.mk _ t) ϑ c
    (fun h0 => hj₀ ((SecMod.eq_zero_iff_coord _).1 h0 j₀))
    (fun z J hJ => sval_pow_of_pullG U (Kbar V) (toUnit _) l θ σ th t hth ht hpow z J hJ) ?_)
  rw [← e]
  exact hact

end GlobalTheory.UU.PrimeIndex
end
