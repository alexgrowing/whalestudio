import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAdditiveCubicalStructureStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem toUnit_left_eq {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

theorem prod_zpow_add {F : Type} [Field F] {I : Type} [Fintype I] (x : I → F) (p q : I → ℤ)
    (hp : ∏ i, x i ^ p i ≠ 0) (hq : ∏ i, x i ^ q i ≠ 0) :
    ∏ i, x i ^ (p i + q i) = (∏ i, x i ^ p i) * ∏ i, x i ^ q i := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => zpow_add' ?_
  rcases eq_or_ne (x i) 0 with h | h
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · by_contra hn
      exact hp (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, zero_zpow _ hn]))
    · by_contra hn
      exact hq (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, zero_zpow _ hn]))
  · exact Or.inl h

theorem tautPt_isAdd : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (a a' : Fin T.r → ℤ) (g g' g'' : GtPtF D F), TautPt T ω s ε n D e β ββ w F a g → TautPt T ω s ε n D e β ββ w F a' g' → TautPt T ω s ε n D e β ββ w F (a + a') g'' → g.IsAdd g' g'' := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF F _ _ a a' g g' g'' hg hg' hg''
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Over.mk ((TF (R := V) F).hom ≫ spMap ω) ⟶ 𝟙_ (Over (Sp W)),
      ρ.left = (TF (R := V) F).hom ≫ spMap ω := ⟨toUnit _, toUnit_left_eq _⟩
  have hpt : ∀ (x : TF (R := V) F ⟶ D.P.A) (b : Fin T.r → ℤ),
      x.left ≫ β = (TF (R := V) F).hom ≫ spMap ω ≫ (T.c₀ b).left → x.left ≫ β = (ρ ≫ T.c₀ b).left :=
    fun x b h => by rw [h, Over.comp_left, hρ, Category.assoc]
  have hb : g''.b = g.b * g'.b := by
    obtain ⟨hpb, hmul⟩ := hF.1
    have e1 := hmul (TF (R := V) F) g.b g'.b (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ a') (hpt _ _ hg.1).symm (hpt _ _ hg'.1).symm
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [hpt _ _ hg''.1, ← e1, ← MonObj.comp_mul, ← T.c₀_add]
    · rw [Over.w, Over.w]
  refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isAdd_iff g g' g'').2 ⟨hb, fun χ y J hJ => ?_⟩
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀, Good T.M.L y J₀ :=
    ⟨fun ψ => (exists_chart T.M.isLB (ψ y)).choose, fun ψ => (exists_chart T.M.isLB (ψ y)).choose_spec⟩
  obtain ⟨k, hk, hv⟩ := hg.2 χ
  obtain ⟨k', hk', hv'⟩ := hg'.2 χ
  obtain ⟨k'', hk'', hv''⟩ := hg''.2 χ
  have v := hv y J₀ J hJ₀ hJ
  have v' := hv' y J₀ J hJ₀ hJ
  have v'' := hv'' y J₀ J hJ₀ hJ
  have hl : lamVal w (lift (DegPre.cF D F χ) g''.b).left y J₀ J =
      lamVal w (lift (DegPre.cF D F χ) (g.b * g'.b)).left y J₀ J := by rw [hb]
  rw [hl] at v''

  have hkk : k'' = k * k' := by
    refine Units.ext ?_
    rw [Units.val_mul, hk'', hk, hk']
    simp only [map_add]
    exact prod_zpow_add _ _ _ (hk ▸ k.ne_zero) (hk' ▸ k'.ne_zero)
  have hG : gm (𝟙 (TF (R := V) F).left) y ⊤ (unitOn k'') =
      gm (𝟙 (TF (R := V) F).left) y ⊤ (unitOn k) * gm (𝟙 (TF (R := V) F).left) y ⊤ (unitOn k') := by
    rw [hkk, unitOn, unitOn, unitOn, map_mul, map_mul]

  have hyc : (DegPre.cF D F χ).left ≫ β = (ρ ≫ T.c₀ ((n : ℤ) • e χ)).left := by
    rw [Over.comp_left, Category.assoc, hF.2.2.2.1 χ, Over.comp_left, hρ, toUnit_left_eq, Category.assoc]
  have wa := (GlobalTheory.T.mumfordBundleIso_additive_cubicalStructure T ε n V D ω s e β ββ w hB hF (TF (R := V) F) g.b g'.b (DegPre.cF D F χ)
    (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ a') (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (hpt _ _ hg.1) (hpt _ _ hg'.1) hyc y J₀ J hJ₀ hJ).2
  simp only [id] at wa

  have C := isCub_cubV T.cub hJ₀ (T := Over.mk ((TF (R := V) F).hom ≫ spMap ω))
  have hC := (C.s01 (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ a')).trans
    (C.s12 (ρ ≫ T.c₀ a) (ρ ≫ T.c₀ ((n : ℤ) • e χ)) (ρ ≫ T.c₀ a'))
  have corr := corr_of_val T.M.isLB
    (t := LB.mulGen T.M.L _ _ _ _ (T.τ₀ (a + a') ((n : ℤ) • e χ))
      (LB.pullGen T.M.L (thφ T.B (x3 T.B)) thε T.cub.t
        (lift (T.c₀ a) (lift (T.c₀ a') (T.c₀ ((n : ℤ) • e χ)))).left))
    (t' := LB.mulGen T.M.L _ _ _ _ (T.τ₀ a ((n : ℤ) • e χ)) (T.τ₀ a' ((n : ℤ) • e χ))) (fun y' J' hJ' =>
      (val_mul hJ' _ _ _).trans (Eq.trans (congrArg (_ * ·) ((val_pull hJ' _ _ _).trans
        (congrArg (fun r => val T.cub.t r y' J') (Category.id_comp _)))) ((T.τ₀_add a a' _ y' J' hJ').trans
          (val_mul hJ' _ _ _).symm)))
  have et := (val_mul hJ₀ _ _ ρ.left).symm.trans ((val_corr hJ₀ corr ρ.left).trans (val_mul hJ₀ _ _ _))
  rw [val_cub T.cub ρ hJ₀] at et
  have sy : ∀ b b', val (T.τ₀ b b') ((TF (R := V) F).hom ≫ spMap ω) y J₀ = val (T.τ₀ b' b) ρ.left y J₀ :=
    fun b b' => (congrArg (fun r => val (T.τ₀ b b') r y J₀) hρ).symm.trans
      (val_corr hJ₀ (corr_of_val T.M.isLB (T.τ₀_symm b b')) ρ.left)
  rw [sy] at v v' v''
  have hth : DVR.th D y J (DVR.cP D (TF (R := V) F) χ) g.b g'.b = cubV D.cub y J (DegPre.cF D F χ) g.b g'.b := rfl
  rw [v, v', v'', hth]
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul hG
  have a₂ := congrArg Additive.ofMul wa
  have a₃ := congrArg Additive.ofMul hC
  have a₄ := congrArg Additive.ofMul et
  simp only [ofMul_mul] at a₁ a₂ a₃ a₄ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ + a₄

end GlobalTheory.TInj
