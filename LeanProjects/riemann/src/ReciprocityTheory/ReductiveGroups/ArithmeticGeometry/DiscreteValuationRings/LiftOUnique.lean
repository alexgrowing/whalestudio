import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem TF_hom : (TF (R := V) F).hom = Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V))) := by
  simp only [TF, jFK, jK]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_liftO (b : TF (R := V) F ⟶ D.toPre.P.A) : ∃ m : TO hϖ hv ⟶ D.toPre.P.A, ιS hϖ hv ≫ m = b := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  obtain ⟨x', hx'p, hx'⟩ := TWO.exists_lift v hϖ hv D.toPre.P.A.hom b.left (by rw [Over.w b, TF_hom])
  exact ⟨Over.homMk x' hx'p, Over.OverMorphism.ext hx'⟩

theorem liftO_unique (m₁ m₂ : TO hϖ hv ⟶ D.toPre.P.A) (h : ιS hϖ hv ≫ m₁ = ιS hϖ hv ≫ m₂) : m₁ = m₂ := by
  haveI : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  apply Over.OverMorphism.ext
  exact TWO.lift_unique v hϖ hv D.toPre.P.A.hom m₁.left m₂.left (Over.w m₁) (Over.w m₂)
    (congrArg (fun g => g.left) h)

def gtφO (m : TO hϖ hv ⟶ D.toPre.P.A) (χ : D.toPre.X) : Fin 4 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(cP D.toPre _ χ * m).left, (cP D.toPre _ χ).left, m.left, (1 : TO hϖ hv ⟶ D.toPre.P.A).left]

def lineφO (m : TO hϖ hv ⟶ D.toPre.P.A) : Fin 2 → ((TO hϖ hv).left ⟶ D.toPre.P.A.left) :=
  ![(1 : TO hϖ hv ⟶ D.toPre.P.A).left, m.left]

def trO (m : TO hϖ hv ⟶ D.toPre.P.A) : TO hϖ hv ⊗ D.toPre.P.A ⟶ TO hϖ hv ⊗ D.toPre.P.A :=
  lift (fst _ _) (padd D.toPre.P.A (snd _ _) (fst _ _ ≫ m))

theorem trO_fst (m : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ fst _ _ = fst _ _ := by
  unfold trO
  exact lift_fst _ _

theorem trO_snd (m : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ snd _ _ = snd _ _ * (fst _ _ ≫ m) := by
  unfold trO
  rw [lift_snd]
  rfl

theorem jO_trO (b : TF (R := V) F ⟶ D.toPre.P.A) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = b) :
    jO hϖ hv (D := D) ≫ trO hϖ hv m = DegPre.trPt D.toPre F b ≫ jO hϖ hv := by
  have h1 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [trO_snd, MonObj.comp_mul, whiskerRight_snd, ← Category.assoc, whiskerRight_fst, Category.assoc, hm]
  have h2 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ snd (TO hϖ hv) D.toPre.P.A =
      snd (TF (R := V) F) D.toPre.P.A * (fst (TF (R := V) F) D.toPre.P.A ≫ b) := by
    rw [whiskerRight_snd]
    unfold DegPre.trPt
    rw [lift_snd]
    rfl
  have h3 : jO hϖ hv (D := D) ≫ trO hϖ hv m ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [trO_fst, whiskerRight_fst]
  have h4 : DegPre.trPt D.toPre F b ≫ jO hϖ hv (D := D) ≫ fst (TO hϖ hv) D.toPre.P.A =
      fst (TF (R := V) F) D.toPre.P.A ≫ ιS hϖ hv := by
    rw [whiskerRight_fst, ← Category.assoc, tr_fst]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc]
    rw [h3, h4]
  · simp only [Category.assoc]
    rw [h1, h2]

theorem gen_uO (k : ℕ) (α α' : D.toPre.X) (m : TO hϖ hv ⟶ D.toPre.P.A)
    (hα : cP D.toPre _ α' = cP D.toPre _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D.toPre _ α * m).left)⁻¹ * h (cP D.toPre _ α).left * h m.left * (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
        (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of V))) (ρ : T ⟶ TO hϖ hv ⊗ D.toPre.P.A) (z : T.left) (J), Good D.toPre.P.L z J →
        val u ρ.left z J = cubN (th D.toPre z J) k (cP D.toPre T α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ snd _ _) *
          (th D.toPre z J (cP D.toPre T α) (ρ ≫ snd _ _) (ρ ≫ fst _ _ ≫ m))⁻¹ * val vO (ρ ≫ fst _ _).left z J := by
  let a : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := cP D.toPre _ α
  let mm : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := fst _ _ ≫ m
  let x : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A := snd _ _
  have hα' : cP D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := by
    rw [← comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A), hα]
    exact (map_mul (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _).trans
      (congrArg₂ (· * ·) (comp_cP D.toPre _ α) (map_pow (preHom (fst (TO hϖ hv) D.toPre.P.A)) _ _))
  obtain ⟨N, hN, vN⟩ := exists_cubN D.toPre.cub a mm x k
  obtain ⟨u₀, hu₀, vu₀⟩ := exists_gen D.toPre.P.isLB (φ' := Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
      (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (ε' := DegPre.deltaε k) (fun U _ h => by
      have p₁ := prod_cub a x mm h
      have p₂ := hF U (fun q => h ((fst (TO hϖ hv) D.toPre.P.A).left ≫ q))
      have p₃ := SectionScalarValuation.prod_famB D.toPre (snd (TO hϖ hv) D.toPre.P.A) α' k h
      have p₄ := SectionScalarValuation.prod_famB D.toPre (trO hϖ hv m ≫ snd _ _) α k h
      have q₁ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α * m).left = (a * mm).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left)
          ((MonObj.comp_mul (fst (TO hϖ hv) D.toPre.P.A) (cP D.toPre _ α) m).trans
            (congrArg (· * mm) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)))
      have q₂ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (cP D.toPre _ α).left = a.left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (comp_cP D.toPre (fst (TO hϖ hv) D.toPre.P.A) α)
      have q₃ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ (1 : TO hϖ hv ⟶ D.toPre.P.A).left =
          (1 : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A).left :=
        congrArg (fun q : TO hϖ hv ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) (fst (TO hϖ hv) D.toPre.P.A))
      have q₄ : (fst (TO hϖ hv) D.toPre.P.A).left ≫ m.left = mm.left := rfl
      rw [q₁, q₂, q₃, q₄] at p₂
      have c₁ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α' = a * mm ^ k := hα'
      have c₂ : SectionScalarValuation.cQ D.toPre (TO hϖ hv ⊗ D.toPre.P.A) α = a := rfl
      rw [c₁] at p₃
      rw [c₂] at p₄
      conv at p₄ => rhs; rw [trO_snd]
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ thK) (K' := K) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := thK) (U := U) _ rfl (prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).symm)
      have r1 : x * (a * mm ^ k) = a * mm ^ k * x := mul_comm _ _
      have r2 : x * mm * a = a * x * mm := by rw [mul_comm, ← _root_.mul_assoc]
      have r3 : mm * x = x * mm := mul_comm _ _
      rw [r1, r2, r3]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, a, mm, x]
      module)
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.mulGen D.toPre.P.L _ _ _ _ N (LB.invGen D.toPre.P.L _ _
      (LB.pullGen D.toPre.P.L (thφ D.toPre.P.A (x3 D.toPre.P.A)) thε D.toPre.cub.t (lift a (lift x mm)).left)))
      (LB.pullGen D.toPre.P.L _ _ vO (fst (TO hϖ hv) D.toPre.P.A).left))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.cub.isGen _)))
      (pullGen_isGen _ _ _ _ hvO _))
  refine ⟨u₀, hu₀, fun T ρ z J hJ => ?_⟩
  refine (vu₀ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    ((congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (val_cub D.toPre.cub ρ hJ _ _ _)))).trans ?_))
    (val_pull hJ _ _ _)))
  rw [← comp_cP D.toPre ρ α]

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
