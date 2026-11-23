import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxesStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lamVal_cmp : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A), D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → IsMonHom b → b.left ≫ β₂ = β₁ → ∀ (χ₁ : D₁.X) (χ₂ : D₂.X), e₁ χ₁ = e₂ χ₂ → ∀ u : LB.Gen (CmpLB D₁ D₂ b χ₁ χ₂), Nrm u → ∀ (Z : Over (Sp V)) (x : Z ⟶ D₁.P.A) (z : Z.left) (J : (Z.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) → (JN D₁ D₂).ι) J₀, Good (JN D₁ D₂) z J → Good T.M.L z J₀ → lamVal w₂ (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left z J₀ (rr J) = lamVal w₁ (lift (toUnit Z ≫ D₁.c χ₁) x).left z J₀ (rl J) * val u x.left z J := by
  intro o W _ _ _ T I _ ε n V _ _ ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hB₁ hB₂ hF₁ hF₂ hb hbβ χ₁ χ₂ hχ u hu Z x z J J₀ hJ hJ₀
  haveI : Nonempty D₁.P.A.left := nonempty_av D₁.P
  haveI : Nonempty D₂.P.A.left := nonempty_av D₂.P
  haveI : Nonempty (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0}) :=
    ⟨(coprod.inl : D₁.P.A.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) (Classical.arbitrary _)⟩
  haveI : Nonempty T.B.left := ⟨β₁ (Classical.arbitrary _)⟩
  have hJN : (JN D₁ D₂).IsLB := jn_isLB D₁ D₂
  have hN : (join (JN D₁ D₂) T.M.L).IsLB := join_isLB hJN T.M.isLB
  have pJ := isPart_inl (JN D₁ D₂) T.M.L
  have pT := isPart_inr (JN D₁ D₂) T.M.L
  have p₁ := pJ.trans (isPart_inl D₁.P.L D₂.P.L)
  have p₂ := pJ.trans (isPart_inr D₁.P.L D₂.P.L)
  obtain ⟨t₁, ht₁, ht₁v⟩ := exists_gen_of_iso pT p₁ w₁ hF₁.2.2.1
  obtain ⟨t₂, ht₂, ht₂v⟩ := exists_gen_of_iso pT p₂ w₂ hF₂.2.2.1
  let m₁ : D₁.P.A.left ⟶ (G2 D₁.P.A).left := (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left
  let m₂ : D₁.P.A.left ⟶ (G2 D₂.P.A).left := (lift (toUnit _ ≫ D₂.c χ₂) b).left
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨J', hJ', eJl, eJr⟩ := exists_good_join hJN T.M.isLB hJ hJ₀
  have key := gen_unique' hN (u := LB.pullGen _ _ _ t₂ m₂)
    (u' := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ t₁ m₁) (pJ.gen u)) ?fe D₁.P.A.hom (eSec D₁.P.A) (Over.w η[D₁.P.A])
    (hG _ _ D₁.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ ht₂ m₂)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₁ m₁) (pJ.gen_isGen hu.1)) ?ev Z.left x.left z J' hJ'
  · rw [val_pull hJ', ht₂v _ _ z J' hJ', val_mul hJ', val_pull hJ', ht₁v _ _ z J' hJ', pJ.val_gen _ _ z hJ'] at key
    have e₁ : x.left ≫ m₁ = (lift (toUnit Z ≫ D₁.c χ₁) x).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have e₂ : x.left ≫ m₂ = (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left := by
      rw [← Over.comp_left, comp_lift, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have r₁ : rs (M := D₁.P.L) (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) J' = rl J := by
      rw [← eJl]; funext ψ
      show Prod.fst (Prod.fst (J' (ψ ≫ coprod.inl ≫ coprod.inl))) = Prod.fst (Prod.fst (J' ((ψ ≫ coprod.inl) ≫ coprod.inl)))
      rw [Category.assoc]
    have r₂ : rs (M := D₂.P.L) (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) J' = rr J := by
      rw [← eJl]; funext ψ
      show Prod.snd (Prod.fst (J' (ψ ≫ coprod.inr ≫ coprod.inl))) = Prod.snd (Prod.fst (J' ((ψ ≫ coprod.inr) ≫ coprod.inl)))
      rw [Category.assoc]
    rw [e₁, e₂] at key
    convert key using 3 <;> first | exact r₁.symm | exact r₂.symm | exact eJl.symm | exact eJr.symm | exact congrArg₂ (isoVal w₂ _ z) eJr.symm r₂.symm | exact congrArg₂ (isoVal w₁ _ z) eJr.symm r₁.symm
  case fe =>
    have g2 : ∀ {a c : D₁.P.A.left ⟶ (G2 T.B).left}, a ≫ (fst T.B T.B).left = c ≫ (fst T.B T.B).left →
        a ≫ (snd T.B T.B).left = c ≫ (snd T.B T.B).left → a = c := fun h1 h2 => pullback.hom_ext h1 h2
    have hT0 : (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left ≫ ββ₁ = (lift (toUnit _ ≫ D₂.c χ₂) b).left ≫ ββ₂ := by
      refine g2 ?_ ?_
      · rw [Category.assoc, Category.assoc, hF₁.2.1.1, hF₂.2.1.1, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Over.comp_left, Over.comp_left, Category.assoc,
          Category.assoc, hF₁.2.2.2.1, hF₂.2.2.2.1, hχ]
      · rw [Category.assoc, Category.assoc, hF₁.2.1.2, hF₂.2.1.2, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, Over.id_left, Category.id_comp, hbβ]
    have hT : m₁ ≫ ββ₁ = m₂ ≫ ββ₂ := hT0
    have eT : ∀ (X : Scheme.{0}) (g : (G2 T.B).left ⟶ X), m₁ ≫ ββ₁ ≫ g = m₂ ≫ ββ₂ ≫ g := fun _ g => by
      rw [← Category.assoc, hT, Category.assoc]
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, eT]
    letI := D₁.P.isAb.comm
    letI := D₂.P.isAb.comm
    have hc₁ : (toUnit D₁.P.A ≫ D₁.c χ₁) * 𝟙 D₁.P.A = 𝟙 D₁.P.A * (toUnit D₁.P.A ≫ D₁.c χ₁) := mul_comm _ _
    have hc₂ : (toUnit D₁.P.A ≫ D₂.c χ₂) * b = b * (toUnit D₁.P.A ≫ D₂.c χ₂) := mul_comm _ _
    have A1 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₁ ≫ (psum D₁.P.A (x2 D₁.P.A) a₂.down).left ≫ coprod.inl ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((𝟙 D₁.P.A * (toUnit _ ≫ D₁.c χ₁)).left ≫ coprod.inl ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₁.c χ₁).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          (h ((𝟙 D₁.P.A : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ := by
      rw [← hc₁, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₁.c χ₁) (𝟙 _) (fun g => h (g ≫ coprod.inl ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    have A2 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₂ ≫ (psum D₂.P.A (x2 D₂.P.A) a₂.down).left ≫ coprod.inr ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((b * (toUnit _ ≫ D₂.c χ₂)).left ≫ coprod.inr ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₂.c χ₂).left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          (h (b.left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₂.P.A).left ≫ coprod.inr ≫ coprod.inl))⁻¹ := by
      rw [← hc₂, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₂.c χ₂) b (fun g => h (g ≫ coprod.inr ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    rw [A1, A2, Fin.prod_univ_four, Fin.prod_univ_four]
    have pm : ∀ {X Y : Over (Sp V)} [GrpObj Y] (a c : X ⟶ Y), padd Y a c = a * c := fun _ _ => rfl
    simp only [DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pm, ← Hom.one_def, Category.assoc]
    simp only [zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  case ev =>
    intro y I hI
    haveI := hb
    rw [val_pull hI, ht₂v _ _ y I hI, val_mul hI, val_pull hI, ht₁v _ _ y I hI, pJ.val_gen _ _ y hI]
    have o₁ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₁.P.A) = η[D₁.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have o₂ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₂.P.A) = η[D₂.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have f₁ : eSec D₁.P.A ≫ m₁ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₁.c χ₁) (1 : 𝟙_ _ ⟶ D₁.P.A)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₁]
    have f₂ : eSec D₁.P.A ≫ m₂ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₂.c χ₂) (1 : 𝟙_ _ ⟶ D₂.P.A)).left := by
      have hbη : η[D₁.P.A] ≫ b = η[D₂.P.A] := IsMonHom.one_hom b
      rw [eSec, ← Over.comp_left, comp_lift, hbη, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₂]
    rw [f₁, f₂]
    have a₂ := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D₂ ω s₂ e₂ β₂ ββ₂ w₂ hB₂ hF₂ (𝟙_ _) (toUnit _ ≫ D₂.c χ₂) y _ _ (pT.good hI)
      (p₂.good hI)).2
    have a₁ := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D₁ ω s₁ e₁ β₁ ββ₁ w₁ hB₁ hF₁ (𝟙_ _) (toUnit _ ≫ D₁.c χ₁) y _ _ (pT.good hI)
      (p₁.good hI)).2
    have c := hu.2 (𝟙_ (Over (Sp V))).left (𝟙 _) y _ (pJ.good hI)
    rw [Category.id_comp] at c
    refine a₂.trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) a₁ c).trans (_root_.mul_one 1)

end GlobalTheory.TInj
