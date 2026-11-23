import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace ClassSumTranslate

section Generic

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)

theorem card_stab (γ : Γ) (y : G) (k : J) :
    Nat.card (Bridge.stab ι J (ι γ * y * k)) = Nat.card (Bridge.stab ι J y) := by
  refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun δ => ?_)
  rw [Bridge.mem_stab, Bridge.mem_stab]
  have e : (ι γ * y * k)⁻¹ * ι δ * (ι γ * y * k) =
      (k : G)⁻¹ * (y⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * y) * k := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right k.2, J.mul_mem_cancel_left (J.inv_mem k.2)]

theorem adInnerIndep : Bridge.AdInnerIndep ι ρ J χ := by
  intro hρ hχ I I' _ _ y y' hy hy' F hF F' hF'
  choose σ hσ using fun i => (hy' (y i)).exists
  have hinj : Function.Injective σ := by
    intro i j hij
    obtain ⟨γ, k, h1⟩ := hσ i
    obtain ⟨γ', k', h2⟩ := hσ j
    refine (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨γ * γ'⁻¹, k'⁻¹ * k, ?_⟩
    rw [h1, h2, hij]; simp [mul_assoc]
  have hsurj : Function.Surjective σ := by
    intro j
    obtain ⟨i, γ, k, h1⟩ := (hy (y' j)).exists
    obtain ⟨γ', k', h2⟩ := hσ i
    refine ⟨i, (hy' (y' j)).unique ⟨γ * γ', k' * k, ?_⟩ ⟨1, 1, by simp⟩⟩
    rw [h1, h2]; simp [mul_assoc]
  unfold Bridge.adInner
  refine Fintype.sum_bijective σ ⟨hinj, hsurj⟩ _ _ fun i => ?_
  obtain ⟨γ, k, h⟩ := hσ i
  rw [h, card_stab, hF γ _ k, hF' γ _ k, inner_smul_left, inner_smul_right, hρ, ← mul_assoc (starRingEnd ℂ _),
    Complex.conj_mul', hχ]
  simp

variable {J} in
theorem stab_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) (y : G) :
    Bridge.stab ι J (y * κ) = Bridge.stab ι J y := by
  ext δ
  rw [Bridge.mem_stab, Bridge.mem_stab, ← hκ (y⁻¹ * ι δ * y)]
  simp [mul_assoc]

variable {J} in
theorem isReps_mul {κ : G} (hκ : ∀ k, κ⁻¹ * k * κ ∈ J ↔ k ∈ J) {I : Type} {y : I → G}
    (hy : Bridge.IsReps ι J y) : Bridge.IsReps ι J fun i => y i * κ := by
  intro h
  refine (existsUnique_congr fun i => ?_).1 (hy (h * κ⁻¹))
  constructor
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨_, (hκ k).2 k.2⟩, ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at e
    rw [e]; simp [mul_assoc]
  · rintro ⟨γ, k, e⟩
    refine ⟨γ, ⟨κ * k * κ⁻¹, (hκ _).1 (by simpa [mul_assoc] using k.2)⟩, ?_⟩
    rw [e]; simp [mul_assoc]

theorem translate (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (κ : l.Q) {F : G → W}
    (hF : F ∈ Bridge.AdForms ι ρ l.J l.χ) :
    (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) ∈ Bridge.AdForms ι ρ l.J l.χ ∧
      Bridge.adInner ι l.J y (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ))
        (fun h => ((l.ch κ : ℂˣ) : ℂ)⁻¹ • F (h * κ)) = Bridge.adInner ι l.J y F F := by
  have hκ : ∀ k, (κ : G)⁻¹ * k * κ ∈ l.J ↔ k ∈ l.J := fun k =>
    ⟨fun h => by simpa [mul_assoc] using hn _ (l.Q.inv_mem κ.2) _ h, hn _ κ.2 _⟩
  constructor
  · intro γ h k
    have e := hF γ (h * κ) ⟨_, (hκ k).2 k.2⟩
    have e2 : l.χ ⟨_, (hκ k).2 k.2⟩ = l.χ k := by
      rw [← l.ch_J, ← l.ch_J]
      have : (⟨(κ : G)⁻¹ * k * κ, l.J_le ((hκ k).2 k.2)⟩ : l.Q) = κ⁻¹ * ⟨k, l.J_le k.2⟩ * κ := rfl
      simp only
      rw [this, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    rw [e2] at e
    simp only
    rw [map_smul, smul_comm, ← e]
    simp [mul_assoc]
  · rw [adInnerIndep ι ρ l.J l.χ hρ (fun k => by rw [← l.ch_J]; exact hch _) I I y _ hy
      (isReps_mul ι hκ hy) F hF F hF]
    unfold Bridge.adInner
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [stab_mul ι hκ, inner_smul_left, inner_smul_right, ← mul_assoc (starRingEnd ℂ _),
      Complex.conj_mul', norm_inv, hch]
    simp

theorem translate_model (l : Bridge.LevDatG G) (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x')
    (hn : ∀ q ∈ l.Q, ∀ k ∈ l.J, q⁻¹ * k * q ∈ l.J) (hch : ∀ q, ‖(l.ch q : ℂ)‖ = 1)
    {I : Type} [Fintype I] {y : I → G} (hy : Bridge.IsReps ι l.J y) (M : Links.HMod (G → W))
    (hM : M.Is (Bridge.AdForms ι ρ l.J l.χ) (Bridge.adInner ι l.J y)) (κ : l.Q) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = ((l.ch κ : ℂˣ) : ℂ)⁻¹ • M.e x (h * κ)) ∧ ‖x'‖ = ‖x‖ := by
  have hx : M.e x ∈ Bridge.AdForms ι ρ l.J l.χ := by
    rw [← hM.2.1]; exact ⟨x, rfl⟩
  obtain ⟨h1, h2⟩ := translate ι ρ l hρ hn hch hy κ hx
  rw [← hM.2.1] at h1
  obtain ⟨x', hx'⟩ := h1
  refine ⟨x', fun h => congrFun hx' h, ?_⟩
  have h3 : inner ℂ x' x' = inner ℂ x x := by
    rw [hM.2.2, hM.2.2, hx']; exact h2
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ x, h3]

end Generic

theorem norm_char {M : Type} [Group M] [Finite M] (c : M →* ℂˣ) (x : M) : ‖(c x : ℂ)‖ = 1 := by
  have h : IsOfFinOrder (((Units.coeHom ℂ).comp c) x) := MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite x)
  exact h.norm_eq_one

variable {D : D7}

theorem norm_levFn (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (x : GL (Fin V.rank) (Lev.EAf D)) : ‖((levFn β (flagL L) x : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) x) = 1 := subgroupCharExtension_one_apply _ _
  have hf : ∀ PP : Pl D.host.E, Finite (kP PP) := fun PP => by
    first | infer_instance | exact Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  unfold levFn
  rw [h2, one_mul, Units.val_mul, norm_mul, Units.coe_prod, Units.coe_prod, norm_prod, norm_prod,
    Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP _
    exact norm_char _ _
  · intro PP _
    rw [Units.coe_prod, norm_prod]
    exact Finset.prod_eq_one fun c _ => norm_char _ _

theorem lev_conj (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {q k : GL (Fin V.rank) (Lev.EAf D)} (hq : q ∈ lev D.sp.cm V.gram β (flagL L))
    (hk : k ∈ lev D.sp.cm V.gram β (flag1L L)) : q⁻¹ * k * q ∈ lev D.sp.cm V.gram β (flag1L L) := by
  have hq' : q ∈ parLev D.sp.cm V.gram β L := hq.1
  have hk' : k ∈ parLev D.sp.cm V.gram β L := hk.1
  have hk2 : rTup β L k ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2
  have h1 : q⁻¹ * k * q ∈ parLev D.sp.cm V.gram β L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq'
  have h2 : rTup β L (q⁻¹ * k * q) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := by
    rw [Subgroup.mem_bot] at hk2 ⊢
    rw [rTup_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hq') hk') hq', rTup_mul (Subgroup.inv_mem _ hq') hk',
      rTup_inv hq', hk2, mul_one, inv_mul_cancel]
  exact ⟨h1, h2⟩

theorem comap_conj {G H : Type} [Group G] [Group H] (f : G →* H) {Q J : Subgroup H}
    (h : ∀ q ∈ Q, ∀ k ∈ J, q⁻¹ * k * q ∈ J) : ∀ q ∈ Q.comap f, ∀ k ∈ J.comap f, q⁻¹ * k * q ∈ J.comap f := by
  intro q hq k hk
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact h _ hq _ hk

theorem levEnv_normal (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ q ∈ (levEnv V β L).Q, ∀ k ∈ (levEnv V β L).J, q⁻¹ * k * q ∈ (levEnv V β L).J :=
  comap_conj (finHom V).range.subtype (comap_conj (Formalism.UG.bc (swapAE D)) fun _ hq _ hk => lev_conj V β L hq hk)

theorem model (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V) (hc : c.Is)
    (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    (g0 : G0 L.Pg L.r) (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (x : M.H) :
    ∃ x' : M.H, (∀ h, M.e x' h = (levChi V β (flagL L) κ)⁻¹ • M.e x (h * (finHom V).rangeRestrict κ)) ∧
      ‖x'‖ = ‖x‖ := by
  have hq : (finHom V).rangeRestrict κ ∈ (levEnv V β L).Q := ⟨hκ.2.1, Subgroup.mem_top _⟩
  exact translate_model (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L)
    (fun γ u v => hc.2.1 _ u v) (levEnv_normal V β L) (fun q => norm_levFn V β L _) hy M hM ⟨_, hq⟩ x

end ClassSumTranslate

theorem translate_unitary_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HV → R.models_cV → ∀ i t g0 κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → ∀ y : (R.HV i t).H, ∃ y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) ∧ ‖y'‖ = ‖y‖ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R _ hH hc i t g0 κ hκ y
  exact ClassSumTranslate.model _ _ _ _ (hc i) _ _ (R.B.L i t).pres.reps (hH i t) g0 κ hκ y

end GlobalTheory
