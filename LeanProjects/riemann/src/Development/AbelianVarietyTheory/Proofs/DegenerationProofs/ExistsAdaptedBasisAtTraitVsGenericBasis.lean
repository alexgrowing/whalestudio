import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMinOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormsOfAdapted
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.GBasis

theorem exists_pull {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : Y' ⟶ Y) (φ₁ : K → (Y' ⟶ X)) (hφ : ∀ a, φ₁ a = h ≫ φ a) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s₁ : LB.Sec (LB.LinComb L φ₁ ε), ∀ (z : Y') J, Good L z J → sval s₁ (𝟙 _) z J = sval s h z J := by
  obtain rfl : φ₁ = fun a => h ≫ φ a := funext hφ
  exact ⟨_, fun z J hJ => (SectionScalarValuation.sval_pullSec φ ε s h (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩

theorem exists_lin_one {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T)
    (b : LB.Sec (LPow G L (N : ℤ) T)) : ∃ s, Lin G L N h (fun _ : Fin 1 => b) (fun _ => 1) s := by
  obtain ⟨s, hs⟩ := exists_pull (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ))
    (h ▷ G).left (fun _ : Fin 1 => (snd T' G).left)
    (fun _ => by rw [← Over.comp_left, whiskerRight_snd]) b
  refine ⟨s, fun z J hJ => (hs z J hJ).trans ?_⟩
  rw [Fin.sum_univ_one, gs_eq _ z ⊤ trivial, map_one, map_one, _root_.one_mul]

theorem fnR_surj {R : Type} [CommRing R] {n : ℕ} (c : Fin n → Γ(Sp R, ⊤)) : ∃ a : Fin n → R, c = fun i => fnR (a i) :=
  ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (c i), funext fun i => by
    simp [fnR]⟩

section Av
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem liftFun_one (W) : liftFun A.A (T := TFK (R := R) F) W ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 1) = 1 := by
  simp only [liftFun, map_one]

theorem eq_of_cmb_one {b t : SecA A F k} (h : Cmb (fun _ : Fin 1 => b) (fun _ => 1) t) : t = b :=
  SecOps.sec_ext fun j => by rw [h j, Fin.sum_univ_one, liftFun_one, _root_.one_mul]

theorem exists_cmb : ∀ {n : ℕ} (b : Fin n → SecA A F k) (a : Fin n → F), ∃ t, Cmb b a t
  | 0, _, _ => ⟨SecOps.secZero, fun j => by rw [Fin.sum_univ_zero]; rfl⟩
  | n + 1, b, a => by
    obtain ⟨t, ht⟩ := exists_cmb (fun i => b i.succ) (fun i => a i.succ)
    refine ⟨SecOps.secAdd (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a 0))) (b 0)) t, fun j => ?_⟩
    rw [Fin.sum_univ_succ, ← ht j]; rfl

variable {M : Type} [AddCommGroup M] [Module F M] {E : SecA A F k → M → Prop}

theorem cmb_rel (hex : ∀ t, ∃ s, E t s)
    (hl : ∀ (t t' t'' : SecA A F k) (s s' : M) (c : F), E t s → E t' s' →
      (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) →
      E t'' (c • s + s')) :
    ∀ {n : ℕ} (b : Fin n → SecA A F k) (s : Fin n → M) (a : Fin n → F) (t : SecA A F k), (∀ i, E (b i) (s i)) →
      Cmb b a t → E t (∑ i, a i • s i)
  | 0, _, _, _, t, _, h => by
    obtain ⟨s, hs⟩ := hex t
    have := hl t t t s s (-1) hs hs (fun j => by rw [h j, Fin.sum_univ_zero, mul_zero, add_zero])
    rw [neg_one_smul, neg_add_cancel] at this
    rwa [Fin.sum_univ_zero]
  | n + 1, b, s, a, t, hb, h => by
    obtain ⟨t', ht'⟩ := exists_cmb (fun i => b i.succ) (fun i => a i.succ)
    have ih := cmb_rel hex hl _ (fun i => s i.succ) _ t' (fun i => hb i.succ) ht'
    rw [Fin.sum_univ_succ]
    exact hl (b 0) t' t _ _ (a 0) (hb 0) ih fun j => by rw [h j, Fin.sum_univ_succ, ht' j]

end Av

theorem card_eq_of_bases {F M : Type} [Field F] [AddCommGroup M] [Module F M] {n m : ℕ} {s : Fin n → M}
    {s' : Fin m → M} (h : ∀ x, ∃! a : Fin n → F, x = ∑ i, a i • s i) (h' : ∀ x, ∃! a : Fin m → F, x = ∑ i, a i • s' i) :
    n = m := by
  have key : ∀ {n : ℕ} {s : Fin n → M}, (∀ x, ∃! a : Fin n → F, x = ∑ i, a i • s i) →
      Nonempty ((Fin n → F) ≃ₗ[F] M) := fun {n s} h =>
    ⟨LinearEquiv.ofBijective (Fintype.linearCombination F s) ⟨fun a b e => (h _).unique
      (Fintype.linearCombination_apply F s a) (e.trans (Fintype.linearCombination_apply F s b)), fun x => by
        obtain ⟨a, ha, -⟩ := h x
        exact ⟨a, (Fintype.linearCombination_apply F s a).trans ha.symm⟩⟩⟩
  obtain ⟨e⟩ := key h
  obtain ⟨e'⟩ := key h'
  simpa using (e.trans e'.symm).finrank_eq

theorem val_nonneg {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) (c : V) :
    (0 : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · simp [hc]
  · obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    have h : HasVal ϖ (algebraMap V (FractionRing V) c) (n : ℤ) :=
      ⟨u, by rw [hu, map_mul, map_pow, zpow_natCast, _root_.mul_comm]⟩
    rw [hv _ _ h]
    exact_mod_cast (Nat.cast_nonneg n : (0 : ℚ) ≤ n)

theorem prim_of {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {r mu : ℕ}
    {cls : Fin r → D.toPre.X} {s : Fin r → Fam D.toPre F 1} (hA : Adapted 1 Q cls mu) (hN : Norms D Q v 1 cls s)
    {c d : Fin r → F} (hc : ∀ i, 0 ≤ v (c i)) (hd : ∀ i, 0 ≤ v (d i)) (hs : ∀ i, s i = d i • ∑ j, c j • s j) :
    Prim D Q v (∑ j, c j • s j) := by
  classical
  have h0 : ∀ i, Q (cls i) = 0 := fun i => by
    have a := hA.1 i (-cls i)
    rw [one_smul, add_neg_cancel, QForm.Q_zero hϖ D hQ] at a
    by_cases e : cls i = 0
    · rw [e, QForm.Q_zero hϖ D hQ]
    · have := QForm.Q_pos hϖ D hQ e
      omega
  have hn : ∀ q : ℚ, NuGe D Q F v 1 (∑ j, c j • s j) q ↔ ∀ i, (q : WithTop ℚ) ≤ v (c i) := fun q => by
    rw [(hN.2 c q).1]
    simp only [h0, Int.cast_zero, zero_div, add_zero]
  refine ⟨(hn 0).2 hc, fun q hq H => ?_⟩
  obtain ⟨i, -⟩ := hA.2.2.1 0
  have e : (Pi.single i 1 : Fin r → F) = fun j => d i * c j := (hN.1 (s i)).unique
    (by simp [Pi.single_apply]) (by rw [hs i, Finset.smul_sum]; simp only [mul_smul])
  have e₁ : (1 : F) = d i * c i := by simpa using congrFun e i
  have e₂ : v (d i) + v (c i) = 0 := by rw [← v.map_mul, ← e₁, v.map_one]
  have e₃ : (q : WithTop ℚ) ≤ 0 := by
    calc (q : WithTop ℚ) = 0 + q := (zero_add _).symm
      _ ≤ v (d i) + v (c i) := add_le_add (hd i) ((hn q).1 H i)
      _ = 0 := e₂
  have : q ≤ 0 := by exact_mod_cast e₃
  linarith

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (χ : Sp V ⟶ Z) (Φ : G.left ⟶ G₀.left) (ω : LB.Iso U.LG.L (L₀.pull Φ)), RigPull G G₀ χ Φ ω U.LG.rig ρ₀ → ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (gam : K →+* FractionRing V) (h : spMap gam ≫ x = jK V ≫ χ) (θ : LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk x))), FrameAt G₀ L₀ 1 x gam χ h (fun _ : Fin 1 => θ) → ∀ (k r : ℕ) (τ : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk x))), 1 ≤ k → AllBasis G₀ L₀ k x τ → ∃ (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w₀ : W0 U.toUnifPre) (th : SecA A F 1) (ϑ : Fam D.toPre F 1) (cls : Fin r → D.toPre.X) (mu : ℕ) (b τF : Fin r → SecA A F k) (s : Fin r → Fam D.toPre F k) (B : Matrix (Fin r) (Fin r) (FractionRing V)), RigPull A.A G₀ (jK V ≫ χ) φ w ρ ρ₀ ∧ NormW U.toUnifPre w₀ ρ ∧ U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ Thru w 1 (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) θ th ∧ (∀ i, Thru w k (T' := TFK (R := V) F) (T := Over.mk x) (jFK (R := V) F ≫ spMap gam) (τ i) (τF i)) ∧ Adapted k Q cls mu ∧ Norms D Q v k cls s ∧ (∀ i, U.ExpandsF F k w₀ (b i) (s i)) ∧ (∀ t, ∃! a, Cmb τF a t) ∧ (∀ i, Cmb τF (B.map (algebraMap (FractionRing V) F) i) (b i)) ∧ BasisBy G₀ L₀ k x gam χ h τ B := by
  intro hLL h1 h2 h3 h4 V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U Z G₀ _ L₀ hL₀ ρ₀ χ Φ ω hRP K _ x gam h θ
    hFr k r τ hk hτ
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨hbij, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hB D A G hG U
  obtain ⟨φ, w, ρ, w₀, hR, hW, hbr⟩ := GlobalTheory.OneBasis.Bridge.exists_bridge Z G₀ L₀ hL₀ ρ₀ V _ D A G U.toUnifPre χ Φ ω hRP
  have cal := GlobalTheory.OneBasis.Calc.main Z G₀ L₀ hL₀ V (jK V ≫ χ) A φ w hR.1 hR.2.1 F
  have lev : ∀ k : ℕ, 1 ≤ k → ∃ (r : ℕ) (cls : Fin r → D.toPre.X) (mu : ℕ)
      (b : Fin r → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk χ))) (bF : Fin r → SecA A F k) (s : Fin r → Fam D.toPre F k),
      BasisAlong G₀ L₀ k (𝟙 _) b ∧
      (∀ i, Thru w k (T' := TFK (R := V) F) (T := Over.mk χ) (jFK (R := V) F ≫ jK V) (b i) (bF i)) ∧
      Adapted k Q cls mu ∧ Norms D Q v k cls s ∧ ∀ i, U.ExpandsF F k w₀ (bF i) (s i) := fun k hk => by
    obtain ⟨r, cls, mu, f, hf, hs⟩ := GlobalTheory.OneBasis.AdaptedFamily.main hLL V ϖ hϖ D Q hQ k hk
    choose s hs using hs F
    obtain ⟨σ, hσ, hσb⟩ := GlobalTheory.OneBasis.ModelBasis.main hLL V D Q A G U k hk r cls mu f hf
    obtain ⟨b, hb, hb'⟩ := hbr k r σ hσb
    choose bF hbF using fun i => ((cal k).1 (Over.mk χ) (jFK (R := V) F ≫ jK V) (Category.assoc _ _ _) (b i)).exists
    exact ⟨r, cls, mu, b, bF, s, hb, hbF, hf.1,
      GlobalTheory.OneBasis.NormsPf.norms_of_adapted hLL h1 h2 h3 h4 V hc ϖ hϖ D Q hQ F v hv k hk r cls mu f s hf hs,
      fun i => hb' i F (f i) (s i) (bF i) (hσ i) (hs i) (hbF i)⟩
  have down : ∀ (k : ℕ) (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk (jK V ≫ χ)))), ∃ t : SecA A F k,
      Thru w k (T' := TFK (R := V) F) (T := Over.mk (jK V ≫ χ)) (spMap (algebraMap (FractionRing V) F)) s t :=
    fun k s => ((cal k).1 (Over.mk (jK V ≫ χ)) (jFK (R := V) F) rfl s).exists
  have one : ∀ (k : ℕ) (T : Over Z) (g : Over.mk (jK V ≫ χ) ⟶ T) b s (bF t : SecA A F k),
      Lin G₀ L₀ k g (fun _ : Fin 1 => b) (fun _ => 1) s →
      Thru w k (T' := TFK (R := V) F) (spMap (algebraMap (FractionRing V) F) ≫ g.left) b bF →
      Thru w k (T' := TFK (R := V) F) (T := Over.mk (jK V ≫ χ)) (spMap (algebraMap (FractionRing V) F)) s t →
      t = bF := fun k T g b s bF t a₁ a₂ a₃ => by
    have := (cal k).2.1 (FractionRing V) (jK V ≫ χ) T g (algebraMap (FractionRing V) F) rfl 1 (fun _ => b)
      (fun _ => 1) s (fun _ => bF) t (by simpa only [fnR, map_one] using a₁) (fun _ => a₂) a₃
    simp only [map_one] at this
    exact eq_of_cmb_one this
  have rel : ∀ (k : ℕ), 1 ≤ k → ∀ {n : ℕ} (b : Fin n → SecA A F k) (s : Fin n → Fam D.toPre F k) (a : Fin n → F)
      (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (b i) (s i)) → Cmb b a t → U.ExpandsF F k w₀ t (∑ i, a i • s i) :=
    fun k hk => cmb_rel (fun t => ((hbij F k hk w₀ hW.1).1 t).exists) (hlin F k w₀)
  have hx : (jFK (R := V) F ≫ spMap gam) ≫ x = jFK (R := V) F ≫ jK V ≫ χ := by rw [Category.assoc, h]

  obtain ⟨th, hth⟩ := ((cal 1).1 (Over.mk x) (jFK (R := V) F ≫ spMap gam) hx θ).exists
  obtain ⟨ϑ, hϑ, hP⟩ : ∃ ϑ, U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ := by
    obtain ⟨r₁, cls₁, mu₁, b₁, bF₁, s₁, hb₁, ht₁, hA₁, hN₁, hE₁⟩ := lev 1 le_rfl
    obtain ⟨b', hb', H⟩ := hFr
    obtain ⟨s₀, l₁, l₂⟩ := H 0
    obtain ⟨t₀, ht₀⟩ := down 1 s₀
    obtain ⟨bF', hbF'⟩ :=
      ((cal 1).1 (Over.mk χ) (jFK (R := V) F ≫ jK V) (Category.assoc _ _ _) (b' 0)).exists
    have e₁ := one 1 _ _ _ _ th t₀ l₁ hth ht₀
    have e₂ := one 1 _ _ _ _ bF' t₀ l₂ hbF' ht₀
    obtain rfl : bF' = th := e₂.symm.trans e₁
    let ga : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
    have hga : spMap ga = jFK (R := V) F ≫ jK V := Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
    have cm : ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ ((1 : ℕ) : ℤ) (Over.mk χ))) (bF : Fin n → SecA A F 1) s t,
        BasisAlong G₀ L₀ 1 (𝟙 _) b →
        (∀ i, Thru w 1 (T' := TFK (R := V) F) (T := Over.mk χ) (jFK (R := V) F ≫ jK V) (b i) (bF i)) →
        Thru w 1 (T' := TFK (R := V) F) (T := Over.mk χ) (jFK (R := V) F ≫ jK V) s t →
        ∃ c : Fin n → F, (∀ i, 0 ≤ v (c i)) ∧ Cmb bF c t := fun n b bF s t a₁ a₂ a₃ => by
      obtain ⟨c, hc⟩ := (a₁ s).exists
      obtain ⟨c, rfl⟩ := fnR_surj c
      rw [← hga] at a₂ a₃
      refine ⟨fun i => ga (c i), fun i => val_nonneg hϖ hv (c i), (cal 1).2.1 V χ (Over.mk χ) (𝟙 _) ga
        (by rw [hga, Category.assoc]) n b c s bF t hc (fun i => ?_) a₃⟩
      have e : spMap ga ≫ (𝟙 (Over.mk χ) : _ ⟶ _).left = spMap ga := Category.comp_id _
      rw [e]
      exact a₂ i
    obtain ⟨c, hc₀, hc₁⟩ := cm _ b₁ bF₁ _ _ hb₁ ht₁ hbF'
    have hE := rel 1 le_rfl bF₁ s₁ c _ hE₁ hc₁
    choose d hd₀ hd₁ using fun i => cm 1 b' (fun _ => bF') _ _ hb'
      (fun j => by rw [Subsingleton.elim j 0]; exact hbF') (ht₁ i)
    refine ⟨_, hE, prim_of hϖ hQ hA₁ hN₁ (d := fun i => d i 0) hc₀ (fun i => hd₀ i 0) fun i => ?_⟩
    have := rel 1 le_rfl (fun _ : Fin 1 => bF') (fun _ => _) (d i) _ (fun _ => hE) (hd₁ i)
    rw [Fin.sum_univ_one] at this
    exact ((hbij F 1 le_rfl w₀ hW.1).1 _).unique (hE₁ i) this

  obtain ⟨r', cls, mu, b, bF, s, hb, ht, hA, hN, hE⟩ := lev k hk
  choose τF hτF using fun i => ((cal k).1 (Over.mk x) (jFK (R := V) F ≫ spMap gam) hx (τ i)).exists
  have hg : spMap ((algebraMap (FractionRing V) F).comp gam) = jFK (R := V) F ≫ spMap gam :=
    Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
  have hbas : ∀ t : SecA A F k, ∃! a, Cmb τF a t :=
    (cal k).2.2 K x ((algebraMap (FractionRing V) F).comp gam) (by rw [hg, hx]) r τ τF hτ (by rw [hg]; exact hτF)
  obtain rfl : r' = r := by
    choose s' hs' using fun i => ((hbij F k hk w₀ hW.1).1 (τF i)).exists
    refine card_eq_of_bases hN.1 (s' := s') fun y => ?_
    obtain ⟨t, ht, hu⟩ := (hbij F k hk w₀ hW.1).2 y
    obtain ⟨a, ha, hau⟩ := hbas t
    refine ⟨a, ((hbij F k hk w₀ hW.1).1 t).unique ht (rel k hk τF s' a t hs' ha), fun a' ha' => hau a' ?_⟩
    obtain ⟨t', ht'⟩ := exists_cmb τF a'
    have := rel k hk τF s' a' t' hs' ht'
    rw [← ha'] at this
    rw [← hu t' this]
    exact ht'
  choose g hg using fun i => exists_lin_one G₀ L₀ k
    (Over.homMk (jK V) rfl : Over.mk (jK V ≫ χ) ⟶ Over.mk χ) (b i)
  have hBi : ∀ i, ∃ c : Fin r' → FractionRing V,
      Lin G₀ L₀ k (Over.homMk (spMap gam) h : Over.mk (jK V ≫ χ) ⟶ Over.mk x) τ (fun j => fnR (c j)) (g i) := fun i => by
    obtain ⟨c, hc⟩ := (hτ (FractionRing V) gam (jK V ≫ χ) h (g i)).exists
    obtain ⟨c, rfl⟩ := fnR_surj c
    exact ⟨c, hc⟩
  choose B hBB using hBi
  refine ⟨φ, w, ρ, w₀, th, ϑ, cls, mu, bF, τF, s, Matrix.of B, hR, hW, hϑ, hP, hth, hτF, hA, hN, hE, hbas, fun i => ?_,
    b, hb, fun i => ⟨g i, hBB i, hg i⟩⟩
  obtain ⟨t, ht'⟩ := down k (g i)
  rw [← one k _ _ _ _ (bF i) t (hg i) (ht i) ht']
  exact (cal k).2.1 (FractionRing V) (jK V ≫ χ) (Over.mk x) _ (algebraMap (FractionRing V) F) rfl r' τ (B i) (g i) τF t
    (hBB i) hτF ht'

end GlobalTheory.GBasis
end
