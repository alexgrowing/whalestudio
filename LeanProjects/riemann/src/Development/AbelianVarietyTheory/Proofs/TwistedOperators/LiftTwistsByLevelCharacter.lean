import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLevChiFlagLEqOne
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowClassSum

section Generic

open Formalism.IndefR.Bridge

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {ι : Γ →* G} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}

theorem card_stab (γ : Γ) (h : G) (k : J) :
    Nat.card (stab ι J (ι γ * h * k)) = Nat.card (stab ι J h) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj γ⁻¹).toEquiv fun δ => ?_)
  have e : (ι γ * h * k)⁻¹ * ι δ * (ι γ * h * k) =
      (k : G)⁻¹ * (h⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * h) * k := by
    simp [mul_assoc]
  rw [mem_stab, mem_stab, e, J.mul_mem_cancel_right k.2, J.mul_mem_cancel_left (J.inv_mem k.2)]

theorem adInner_indep (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y y' : I → G} (hy : IsReps ι J y) (hy' : IsReps ι J y')
    {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ) :
    adInner ι J y' F F' = adInner ι J y F F' := by
  choose s γ k hs using fun i => (hy (y' i)).exists
  have hinj : Function.Injective s := by
    intro i j hij
    refine (hy' (y' i)).unique ⟨1, 1, by simp⟩ ⟨γ i * (γ j)⁻¹, (k j)⁻¹ * k i, ?_⟩
    rw [hs i, hs j, hij]
    simp [mul_assoc]
  unfold adInner
  refine Fintype.sum_bijective s (Finite.injective_iff_bijective.1 hinj) _ _ fun i => ?_
  rw [hs i, card_stab, hF, hF', inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _),
    Complex.conj_mul', hχ, hρ]
  simp

variable {Q : Subgroup G} {ch : Q →* ℂˣ}

theorem reductionGroupAction_mem_adelicForms (hJ : J ≤ Q) (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    (κ : Q) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) : g0Act ch κ F ∈ AdForms ι ρ J χ := by
  intro γ h k
  have hk := hn κ κ.2 k k.2
  have e : ι γ * h * k * κ = ι γ * (h * κ) * ((⟨_, hk⟩ : J) : G) := by simp [mul_assoc]
  have e2 : χ ⟨_, hk⟩ = χ k := by
    rw [← hch, ← hch]
    have : (⟨_, hJ hk⟩ : Q) = κ⁻¹ * ⟨k, hJ k.2⟩ * κ := rfl
    rw [this, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  unfold g0Act
  rw [e, hF, e2, map_smul, smul_comm]

theorem adInner_g0Act (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (κ : Q) (hκ : ‖(ch κ : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι J y)
    {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ) :
    adInner ι J y (g0Act ch κ F) (g0Act ch κ F') = adInner ι J y F F' := by
  have hn' : ∀ k ∈ J, (κ : G) * k * (κ : G)⁻¹ ∈ J := fun k hk => by
    simpa using hn _ (Q.inv_mem κ.2) k hk
  have hy' : IsReps ι J fun i => y i * κ := by
    intro h
    refine (existsUnique_congr fun i => ?_).1 (hy (h * (κ : G)⁻¹))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, ⟨_, hn κ κ.2 k k.2⟩, ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at e
      rw [e]; simp [mul_assoc]
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, ⟨_, hn' k k.2⟩, ?_⟩
      rw [e]; simp [mul_assoc]
  rw [← adInner_indep hρ hχ hy hy' hF hF']
  unfold adInner g0Act
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : stab ι J (y i * κ) = stab ι J (y i) := by
    ext δ
    rw [mem_stab, mem_stab]
    constructor
    · intro h
      simpa [mul_assoc] using hn' _ h
    · intro h
      simpa [mul_assoc] using hn κ κ.2 _ h
  rw [hs, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _), Complex.conj_mul',
    Units.val_inv_eq_inv_val, norm_inv, hκ]
  simp

theorem exists_g0Act (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hn1 : ∀ q, ‖(ch q : ℂ)‖ = 1)
    (hJ : J ≤ Q) (hn : ∀ κ ∈ Q, ∀ k ∈ J, κ⁻¹ * k * κ ∈ J) (hch : ∀ k : J, ch ⟨k, hJ k.2⟩ = χ k)
    {I : Type} [Fintype I] {y : I → G} (hy : IsReps ι J y) (M : Links.HMod (G → W))
    (hM : M.Is (AdForms ι ρ J χ) (adInner ι J y)) (κ : Q) (x : M.H) :
    ∃ x' : M.H, M.e x' = g0Act ch κ (M.e x) ∧ ‖x'‖ = ‖x‖ := by
  obtain ⟨-, hr, hi⟩ := hM
  have hχ : ∀ k, ‖(χ k : ℂ)‖ = 1 := fun k => by
    rw [← hch]; exact hn1 _
  have hx : M.e x ∈ AdForms ι ρ J χ := by
    rw [← hr]; exact ⟨x, rfl⟩
  have hm := reductionGroupAction_mem_adelicForms hJ hn hch κ hx
  rw [← hr] at hm
  obtain ⟨x', hx'⟩ := hm
  refine ⟨x', hx', ?_⟩
  have e : inner ℂ x' x' = inner ℂ x x := by
    rw [hi, hi, hx']
    exact adInner_g0Act hρ hχ hn κ (hn1 _) hy hx hx
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, e]

theorem twistedTranslate_apply_eq_inv_smul {a : G} (ha : a ∈ Q) (F : G → W) (h : G) {z : ℂ} (hz : ((ch ⟨a, ha⟩ : ℂˣ) : ℂ) = z) :
    g0Act ch ⟨a, ha⟩ F h = z⁻¹ • F (h * a) := by
  rw [← hz, ← Units.val_inv_eq_inv_val]
  rfl

end Generic

variable {D : D7}

theorem norm_levFn_flagL (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Lev.EAf D)) : ‖((levFn β (flagL L) x : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : Formalism.L2.DIV.ext1 (flagL L).P.H (flagL L).P.chi (Formalism.L2.DIV.rTup β (flagL L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h2, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod, norm_prod,
    Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_residueChar_eq_one PP _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_residueChar_eq_one PP _ _

theorem conj_mem_flag1L (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {a b : GL (Fin V.rank) (Lev.EAf D)} (ha : a ∈ lev D.sp.cm V.gram β (flagL L))
    (hb : b ∈ lev D.sp.cm V.gram β (flag1L L)) : a⁻¹ * b * a ∈ lev D.sp.cm V.gram β (flag1L L) := by
  have h1 : a ∈ parLev D.sp.cm V.gram β L := ha.1
  have h2 : b ∈ parLev D.sp.cm V.gram β L := hb.1
  have h3 : rTup β L b = 1 := Subgroup.mem_bot.1 hb.2
  have h4 : a⁻¹ * b ∈ parLev D.sp.cm V.gram β L := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2
  have h5 : rTup β L (a⁻¹ * b * a) = 1 := by
    rw [rTup_mul h4 h1, rTup_mul (Subgroup.inv_mem _ h1) h2, rTup_inv h1, h3, mul_one, inv_mul_cancel]
  exact ⟨Subgroup.mul_mem _ h4 h1, Subgroup.mem_bot.2 h5⟩

theorem levEnv_normal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ κ ∈ (levEnv V β L).Q, ∀ k ∈ (levEnv V β L).J, κ⁻¹ * k * κ ∈ (levEnv V β L).J := by
  intro κ hκ k hk
  have h := conj_mem_flag1L V β L (a := Formalism.UG.bc (swapAE D) κ.1) (b := Formalism.UG.bc (swapAE D) k.1) hκ hk
  rw [← map_inv, ← map_mul, ← map_mul] at h
  exact h

theorem levEnv_ch (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl

theorem mem_levEnv_Q {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g0 : G0 L.Pg L.r} {κ : GA D V} (hκ : IsLevelLift V β L g0 κ) :
    (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q := by
  have h : finE V κ ∈ lev D.sp.cm V.gram β (flagL L) := ⟨hκ.2.1, Subgroup.mem_top _⟩
  exact h

theorem levEnv_ch_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {κ : GA D V} (hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q) :
    (((levEnv V β L).ch ⟨_, hq⟩ : ℂˣ) : ℂ) = levChi V β (flagL L) κ := by
  rw [levEnv_ch]
  rfl

theorem exists_translate (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (c : CoefA V) (hc : c.Is) (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = (levChi V β (flagL L) κ)⁻¹ • M.e x (h * (finHom V).rangeRestrict κ)) ∧
      ‖x'‖ = ‖x‖ := by
  have hq := mem_levEnv_Q hκ
  have hch : ∀ q, ‖(((levEnv V β L).ch q : ℂˣ) : ℂ)‖ = 1 := fun q => by
    rw [levEnv_ch]; exact norm_levFn_flagL V β L _
  have hρ : ∀ (γ : GQ V) (u u' : c.W),
      inner ℂ ((c.ρ.comp (GQ V).subtype) γ u) ((c.ρ.comp (GQ V).subtype) γ u') = inner ℂ u u' :=
    fun γ u u' => hc.2.1 γ.1 u u'
  have key : ∃ x' : M.H, M.e x' = Bridge.g0Act (levEnv V β L).ch ⟨_, hq⟩ (M.e x) ∧ ‖x'‖ = ‖x‖ :=
    exists_g0Act (W := c.coef.W) (ι := Bridge.ratF V) (ρ := c.coef.ρ) (χ := (levEnv V β L).χ)
      (ch := (levEnv V β L).ch) hρ hch (levEnv V β L).J_le (levEnv_normal V β L) (levEnv V β L).ch_J hy M hM ⟨_, hq⟩ x
  obtain ⟨x', hx', hn⟩ := key
  refine ⟨x', fun h => ?_, hn⟩
  refine Eq.trans ?_ (twistedTranslate_apply_eq_inv_smul (ch := (levEnv V β L).ch) hq (M.e x) h (levEnv_ch_lift hq))
  exact congrFun hx' h

end GlobalTheory.RowClassSum

namespace GlobalTheory

theorem rowForms_translate_unitary : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HX → R.models_cX → ∀ t g0 κ, IsLevelLift D.sp.X' R.βX (R.datXt t) g0 κ → ∀ y : (R.HX t).H, ∃ y' : (R.HX t).H, (∀ h, (R.HX t).e y' h = (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ • (R.HX t).e y (h * (finHom _).rangeRestrict κ)) ∧ ‖y'‖ = ‖y‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hH hc t g0 κ hκ y
  exact RowClassSum.exists_translate _ R.βX (R.datXt t) R.cX hc (R.HX t) _ (R.B.R t).pres.reps (hH t) g0 κ hκ y

end GlobalTheory
