import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedPullbackConjugateTranslateEqTranslateL

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.DivLevel
open GlobalTheory.ConjPull GlobalTheory.OneOrder GlobalTheory.AlphaForm

theorem isVtOver_of_isNormPull_dvd {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)
    (φ ψ : A ⟶ A) [IsMonHom ψ] (N M m : ℕ) (hm : M * M = N * m)
    (hN : ψ ≫ φ = 𝟙 A ^ M) {T : Over S} (ok : (T ⟶ A) → Prop) (t : T ⟶ A) (ho : ok t) (ht : t ^ (M * M) = 1)
    (s : LB.Sec (LPow A L.L 1 T)) (hh : LB.Sec (LPow A L.L (N : ℤ) T)) (Fs : LB.Sec (LPow A L.L ((M : ℤ) ^ 2) T))
    (h₁ : IsTransPull A L φ N s (t ≫ ψ) hh) (h₂ : IsNormPull A L ψ ((M : ℤ) ^ 2) (N : ℤ) hh Fs) :
    IsVtOver A L M ok s (t ^ M) Fs := by
  have hL := L.isLB
  obtain ⟨s₀, ⟨α₀, α, gα₀, nα, cα, tα⟩, hb, U, hU, aU⟩ := h₁
  obtain ⟨β₀, β, gβ₀, nβ, cβ, tβ⟩ := h₂
  obtain ⟨u', g, sl, hv⟩ := exists_symLift_pull hL ψ β₀ gβ₀ t U hU hb (m := m) (by rw [← hm]; exact ht)
  have hUp := hU.pt_eq
  have e₀ : ψ.left ≫ φ.left = (mulA A M).left := by rw [← Over.comp_left, hN]
  have ha : eSec A ≫ ψ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨κ₀, gκ₀, vκ₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A M).left]) (ε' := ![(M : ℤ) ^ 2, -1])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ β₀ (LB.pullGen L.L _ _ α₀ ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ gβ₀ (DVR.pullGen_isGen _ _ _ _ gα₀ _))
  have e₁ : (snd T A).left ≫ (mulA A M).left = (snd T A ^ M).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨κ, gκ, vκ⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ M).left]) (ε' := ![(M : ℤ) ^ 2, -1])
    (fun U _ f => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id])
    (LB.pullGen L.L ![𝟙 A.left, (mulA A M).left] ![(M : ℤ) ^ 2, -1] κ₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ gκ₀ _)
  obtain ⟨s₁, tκ, -⟩ := existsUnique_isTwistPull S A L.L hL T (mulT A T M) (snd T A ^ M) (lift_snd _ _)
    ((M : ℤ) ^ 2) 1 κ gκ s
  refine ⟨t, κ₀, κ, s₁, ⟨t, u', g⟩, rfl, ho, gκ₀, corr_of_val hL fun y J hJ => ?_,
    corr_of_val hL fun y J hJ => vκ _ _ y J hJ, tκ, by rw [pow_two M, hm]; exact sl, twist_of_val hL g fun z J hJ => ?_⟩
  · have a₁ := val_corr hJ nα (𝟙 _)
    have a₂ := val_corr hJ nβ (𝟙 _)
    have vr : ∀ k : ℤ, val (rigPow A L.L L.rig k) (𝟙 _) y J = val (L := L.L) L.rig (𝟙 _) y J ^ k :=
      fun k => map_zpow _ _ _
    rw [val_pull hJ, val_mul hJ, vr, vr] at a₁ a₂
    rw [val_pull hJ, vκ₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, ha, a₁, a₂, val_mul hJ, vr]
    refine Eq.trans ?_ (congrArg _ (val_inv _ _).symm)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
    module
  · have c₁ : endOver A T ψ ≫ translPt A (t ≫ ψ) = translPt A t ≫ ψ := by
      rw [translPt_eq, translPt_eq, MonObj.comp_mul, MonObj.mul_comp, lift_fst_assoc, lift_snd, Category.assoc]
    have c₂ : endOver A T ψ ≫ translT A U.pt ≫ snd T A = translPt A t ≫ ψ := by
      rw [hUp, translT, lift_snd, c₁]
    have c₃ : endOver A T ψ ≫ translT A U.pt ≫ endOver A T φ = translT A t ≫ mulT A T M := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [translT, mulT]
      · have : endOver A T φ ≫ snd T A = snd T A ≫ φ := lift_snd _ _
        rw [Category.assoc, Category.assoc, this, ← Category.assoc (translT A U.pt), ← Category.assoc, c₂,
          Category.assoc, hN, mulT, Category.assoc, lift_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
          translT, lift_snd]
    have c₆ : translT A t ≫ snd T A = translPt A t := lift_snd _ _
    rw [twist_val tβ _ z hJ, twist_val aU _ z hJ, twist_val tα _ z hJ]
    dsimp only
    rw [twist_val tκ _ z hJ, hv _ _ z J hJ, vκ _ _ z J hJ, val_corr hJ cα, val_corr hJ cβ, val_pull hJ, val_pull hJ,
      val_pull hJ, vκ₀ _ _ z J hJ, val_mul hJ, val_pull hJ]
    simp only [Category.id_comp, ← Over.comp_left, Category.assoc, c₂, c₃, c₆]
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
    rw [_root_.mul_assoc _ _⁻¹, inv_mul_cancel_left]

theorem isVtOver_conj_pull_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E) (N k : ℕ), l.M = N * k → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G) (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (N : ℤ) (ptO Xo xF))), b ≫ Xo.univ.t.act.act (star α) = 1 → IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N s b hh → ∃ Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo xF)), IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act ((k : 𝓞 E) * star α)) ((l.M : ℤ) ^ 2) (N : ℤ) hh Fs ∧ IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (b ≫ Xo.univ.t.act.act α) Fs := by
  intro E _ _ _ H Dw l Xo F _ _ xF α N k hk hα hMb s b hh hb h
  letI := H.starRing
  have := UnivPol.isLocallyNoetherian Xo
  have hom := Xo.univ.t.act.hom
  have := hom α
  have := hom ((k : 𝓞 E) * star α)
  have hL := Xo.univ.t.PP.isLB
  have hβ' : ((k : 𝓞 E) * star α) * star ((k : 𝓞 E) * star α) = ((k * l.M : ℕ) : 𝓞 E) := by
    rw [star_mul, star_star, star_natCast, hk]
    push_cast
    rw [← hα]
    ring
  have hαβ : α * ((k : 𝓞 E) * star α) = (l.M : 𝓞 E) := by
    rw [hk]
    push_cast
    rw [← hα]
    ring
  have hM : 0 < l.M := l.odd.pos
  have hg := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 ((k : 𝓞 E) * star α)
    (k * l.M) hβ' (Xo.univ.t.adj _) Xo.univ.t.prim N
  have hMM : l.M * l.M = N * (k * l.M) := by rw [← _root_.mul_assoc, ← hk]
  obtain ⟨β, hβ⟩ := hg.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act ((k : 𝓞 E) * star α)).left]
    ![(l.M : ℤ) ^ 2, -(N : ℤ)] (by rw [pow_two, ← Nat.cast_mul, hMM]; rfl)
  obtain ⟨Fs, hFs⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act ((k : 𝓞 E) * star α)) _ _ β hβ hh
  refine ⟨Fs, hFs, ?_⟩
  have hbM : b ^ l.M = 1 := by
    rw [hk, pow_mul, h.pow_eq_one, one_pow]
  have hkill : ∀ x : 𝓞 E, star α ∣ x → b ≫ Xo.univ.t.act.act x = 1 := by
    rintro _ ⟨d, rfl⟩
    have := hom d
    rw [Xo.univ.t.act.mul, ← Category.assoc, hb, MonObj.one_comp]
  obtain ⟨-, I, -⟩ := Xo.univ.geom F xF (Spec.preimage (xF ≫ Xo.s)).hom (Spec.map_preimage _).symm
  obtain ⟨a, ha⟩ := (I.onto l.M hM b).1 hbM
  have hr : I.ev (l.M * l.M) a ^ l.M = b := (I.tower l.M l.M hM hM a).trans ha
  have hz : ∀ x : 𝓞 E, I.ev (l.M * l.M) a ≫ Xo.univ.t.act.act ((l.M : 𝓞 E) * x) = b ≫ Xo.univ.t.act.act x :=
    fun x => by rw [Xo.univ.t.act.mul, ← Category.assoc, comp_act_natCast, hr]
  obtain ⟨m, hm, e, he, hme⟩ := Submodule.mem_sup.1 (l.coprime.ge (Submodule.mem_top (x := (1 : 𝓞 E))))
  obtain ⟨t, ht, ho⟩ : ∃ t : ptO Xo xF ⟶ Xo.univ.t.G, t ≫ Xo.univ.t.act.act ((k : 𝓞 E) * star α) = b ∧
      KilledBy Xo (l.Mb ^ 2) t := by
    refine ⟨I.ev (l.M * l.M) a ≫ Xo.univ.t.act.act (α * e), ?_, fun x hx => ?_⟩
    · rw [Category.assoc, ← Xo.univ.t.act.mul, mul_right_comm, hαβ, hz]
      have h1 : b ≫ Xo.univ.t.act.act (m + e) = b := by rw [hme, Xo.univ.t.act.one, Category.comp_id]
      rwa [Xo.univ.t.act.add, MonObj.comp_mul, hkill m (Ideal.mem_span_singleton.1 (hMb hm)), _root_.one_mul] at h1
    · have h1 : e * x ∈ Ideal.span {(l.M : 𝓞 E) * star α} := by
        have h2 := Ideal.mul_mem_mul he hx
        rw [pow_two, ← _root_.mul_assoc, mul_comm (Ideal.map _ l.Mb) l.Mb, l.prod] at h2
        rw [← Ideal.span_singleton_mul_span_singleton]
        exact Ideal.mul_mono_right hMb h2
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h1
      rw [Category.assoc, ← Xo.univ.t.act.mul, _root_.mul_assoc, hd,
        show α * ((l.M : 𝓞 E) * star α * d) = (l.M : 𝓞 E) * (star α * (α * d)) by ring, hz]
      exact hkill _ ⟨_, rfl⟩
  have hN : Xo.univ.t.act.act ((k : 𝓞 E) * star α) ≫ Xo.univ.t.act.act α = 𝟙 _ ^ l.M := by
    rw [← Xo.univ.t.act.mul, mul_comm, hαβ, ← comp_act_natCast Xo.univ.t.act, Category.id_comp]
  have htM : t ^ l.M = b ≫ Xo.univ.t.act.act α := by
    rw [← ht, Category.assoc, hN, MonObj.comp_pow, Category.comp_id]
  rw [← htM]
  refine isVtOver_of_isNormPull_dvd Xo.univ.t.PP _ _ N l.M _ hMM hN _ t ho ?_ s hh Fs (ht.symm ▸ h) hFs
  rw [pow_mul, htM, ← MonObj.pow_comp, hbM, MonObj.one_comp]

theorem alphaForm_at_point_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (α : 𝓞 E) (N : ℕ), N ∣ l.M → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (n : ℕ) (b : Fin n → (ptO Xo yF.x ⟶ Xo.univ.t.G)) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (N : ℤ) (ptO Xo yF.x))), (∀ i, b i ≫ Xo.univ.t.act.act (star α) = 1) → (∀ i, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N yF.s (b i) (hh i)) → ∃ (xx : Fin n → Dw.La) (Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x))), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (N : ℤ) (hh i) (colOf m i) = algebraMap c.F F (nrm Dw c a α) * thExpr Xo c nab yF Pp Fs := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab F _ _ _ yF α N ⟨k, hk'⟩ hα hMb n b hh hb hT
  choose Fs hN hV using fun i => isVtOver_conj_pull_dvd E H Dw l Xo F yF.x α N k hk' hα hMb yF.s (b i) (hh i) (hb i) (hT i)
  have hk : ∀ i, KilledBy Xo l.Mb (b i ≫ Xo.univ.t.act.act α) := by
    intro i x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 (hMb hx)
    haveI := Xo.univ.t.act.hom (α * y)
    rw [Category.assoc, ← Xo.univ.t.act.mul, show α * (y * star α) = star α * (α * y) by ring,
      Xo.univ.t.act.mul, ← Category.assoc, hb i, MonObj.one_comp]
  choose xx hxx using fun i => GlobalTheory.T.exists_levelPoint_eq_of_killedByHalfLevel E H Dw l Xo c F yF _ (hk i)
  refine ⟨xx, Fs, fun i => (hxx i) ▸ hV i, fun a Pp hP => ?_⟩
  by_cases h0 : Pp = 0
  · subst h0
    simp [thExpr]
  have hβ : ((k : 𝓞 E) * star α) * star ((k : 𝓞 E) * star α) = ((k * l.M : ℕ) : 𝓞 E) := by
    rw [star_mul, star_star, star_natCast, hk']
    push_cast
    rw [← hα]
    ring
  have hαβ : α * ((k : 𝓞 E) * star α) = (l.M : 𝓞 E) := by
    rw [hk']
    push_cast
    rw [← hα]
    ring
  have hch := GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab F yF ((k : 𝓞 E) * star α) (k * l.M) N ((l.M : ℤ) ^ 2) hβ
    (by rw [← _root_.mul_assoc, ← hk']; push_cast; ring) n hh Fs hN a Pp hP
  have hM : (l.M : c.F) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  unfold thExpr
  rw [hch, ← _root_.mul_assoc, ← _root_.mul_assoc, ← map_mul, ← map_mul, totalDegree_harm c hP h0,
    mul_right_comm, nrm_mul_nrm Dw c a α _ l.M hαβ, mul_inv_cancel₀ (pow_ne_zero _ hM), map_one, _root_.one_mul]

set_option maxHeartbeats 1600000 in

theorem harmonicValue_translate_dvd_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N ∣ l.M → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (_ : N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∃ (xx : Fin n → Dw.La) (u : F), v u = 0 ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 q h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (io (nrm Dw c a α) * evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C P htors ϖ hϖ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hx ho
    α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t q e₀ hNq σ' h hw hfo hq hphi hsm hexp hgerm hkill
  subst hNq
  have hodd : Odd N := Odd.of_dvd_nat l.odd hN
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] F := { algebraMap T.Fr F with commutes' := fun _ => rfl }
  have hφ : φ.toRingHom = algebraMap T.Fr F := rfl
  have hM : 1 ≤ N := hodd.pos
  obtain ⟨yF, hyF⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T.Fr F φ y.1
  obtain ⟨τ, hτ, hEL, -⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT
    C.eT C.wPT C.chartT C.frameT C.primT
  obtain ⟨θ₁, θα₁, hθ₁, hθα₁, hone⟩ := GlobalTheory.OneColTranslate.oneColumn_translate E H Dw l Xo c T io y.1 C.I P ϖ hϖ F φ hφ
    yF hyF α N hodd hα
  obtain ⟨u, p₁, w₁, ζ₁, r₀, r, σ₁, S, hu, hS, htS, hcol⟩ := translate_eq_box E H Dw l Xo c T io y C P htors ϖ hϖ F v hv
    n D' A' G' pD pA pG U' PU oD' hx ho α N hM hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀ t N (one_mul _) hw hfo hq
    hphi hsm
  rw [htS] at hexp
  have hone' := fun i => hone (p₁ i) (w₁ i) (ζ₁ i) (x ≫ pA.pr i) (r₀ i) (r i) (σ₁ i) (hcol i).1 (hcol i).2.1
    (hcol i).2.2.1 (by rw [Category.assoc]; exact hkill i) (hcol i).2.2.2.1 (hcol i).2.2.2.2.1 (hcol i).2.2.2.2.2
  choose u₁ b hs σ₀ hu₁ hb htp htie hσ using hone'
  obtain ⟨xx, Fs, hFs, hal⟩ := alphaForm_at_point_dvd E H Dw l Xo c nab hnab F yF α N hN hα hMb n b hs hb htp
  refine ⟨xx, u * ∏ i, u₁ i, ?_, fun a Pp hPp f hf' => ?_⟩
  · rw [v.map_mul, hu, zero_add]
    refine val_prod_eq_zero v _ _ fun i => ?_
    obtain ⟨m, hm, hm'⟩ := hu₁ i
    exact ColumnSplit.val_eq_zero_of_pow_eq_one v hm hm'
  · set m := Pp.totalDegree with hm
    choose a₀ ha₀ using fun i => exists_jetAt P.U.toUnifPre F (κ := Fin 1 × Fin (chD C.ch)) C.xT m (τ m) (hτ m) N (σ₀ i)
    choose a₁ ha₁ using fun i => exists_jetAt P.U.toUnifPre F (κ := Fin 1 × Fin (chD C.ch)) C.xT m (τ m) (hτ m) N (σ₁ i)
    choose f₀ hf₀ using fun i => GlobalTheory.ChartCmp.FrameRatio.psJet_surj m (a₀ i)
    have ha : ∀ i, a₁ i = algebraMap F _ (u₁ i) * a₀ i := fun i =>
      jetAt_smul P.U.toUnifPre F m (C.xT m) (τ m) N (σ₀ i) (σ₁ i) (u₁ i) _ _ (hσ i) (ha₀ i) (ha₁ i)
    have hj := psJet_of_box P C.actT C.xT C.eT C.wPT τ hτ hEL n D' A' G' pD pA pG U' PU F N hM m σ₁ _ a₁ σ' S u h
      (fun i => (hcol i).2.2.2.2.2) ha₁ hS hexp hgerm
    have hj' : psJet m h = psJet m (∑ _i : Fin 1, (u * ∏ i, u₁ i) • boxSer f₀) := by
      rw [GermBasic.psJet_sum, Fin.sum_univ_one, BoxGerm.psJet_boxSer, hj]
      simp only [ha, hf₀, map_mul, AlgHom.commutes, Finset.prod_mul_distrib, map_prod, _root_.mul_assoc]
    have h1 := harmonic_value_at E H Dw l Xo c nab hnab T io y C P τ hEL F φ hφ yF hyF N n m σ₀ hs f₀ htie
      (fun i => by rw [hf₀]; exact ha₀ i) a Pp hPp le_rfl
    have h2 := hal a Pp hPp
    have h3 : algebraMap T.Fr F (evI y f) = thExpr Xo c nab yF Pp Fs := by
      first
        | exact GlobalTheory.PtTie.evI_eq_thExpr_ext (chartIndep2_of_glob GlobalTheory.firstFiveLaws.1.globalFns) E H Dw l Xo c nab hnab T
            io y F φ hφ yF hyF a n xx Pp hPp Fs hFs f hf'
        | exact GlobalTheory.PtTie.evI_eq_thExpr_ext E H Dw l Xo c nab hnab T io y F φ hφ yF hyF a n xx Pp hPp Fs hFs f hf'
    have h0 := nabJet T.Fr (chD C.ch) (𝓞 E) C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 N n
      (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
    have h4 := h0.2.1 (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) (Fin 1) (fun _ => u * ∏ i, u₁ i)
      (fun _ => boxSer f₀)
    have hdeg : (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp).totalDegree ≤ m :=
      Finset.sup_mono (MvPolynomial.support_map_subset _ _)
    have h5 := h0.1 (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) h _
      fun e he => HarmInvA.coeff_eq_of_psJet hj' (he.trans hdeg)
    rw [h5, h4, Fin.sum_univ_one, map_mul, h3]
    congr 1
    exact h1.symm.trans h2

theorem val_nonneg_of_isIntegral {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {x : F} (hx : IsIntegral ℤ x) :
    0 ≤ v x :=
  (Valuation.integer.integers (AddValuation.toValuation v)).mem_of_integral hx.tower_top

set_option maxHeartbeats 1600000 in

theorem harmonicValue_translate_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (IsLocalRing.maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (IsLocalRing.maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N ∣ l.M → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (σ' : U'.toUnifPre.SecGF F (1 * N)) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F (1 * N) σ' t → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * N) σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∃ (xx : Fin n → Dw.La) (u : F), 0 ≤ v u ∧ ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C _ P htors _ ϖ hϖ Q _ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hx ho
    α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t σ' h hw _ hfo hq hphi hsm hexp hgerm hkill a Pp hPp
  obtain ⟨xx, u, hu, hval⟩ := harmonicValue_translate_dvd_unit E H Dw l Xo c nab hnab T io y C P htors ϖ hϖ F v hv
    n D' A' G' pD pA pG U' PU oD' hx ho α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t (1 * N) rfl (one_mul N).symm σ' h
    hw hfo hq hphi hsm hexp hgerm hkill
  refine ⟨xx, u * algebraMap T.Fr F (io (nrm Dw c a α)), ?_, fun f hf => ?_⟩
  · rw [v.map_mul, hu, zero_add]
    refine val_nonneg_of_isIntegral v (map_isIntegral_int _ (map_isIntegral_int _ ?_))
    exact IsIntegral.prod _ fun τ _ => (map_isIntegral_int _ (Algebra.IsIntegral.isIntegral α)).pow _
  · rw [hval a Pp hPp f hf, map_mul, _root_.mul_assoc]

end GlobalTheory.DivLevel
