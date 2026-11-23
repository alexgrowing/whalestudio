import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThetaSwapFirstTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubicalLawRight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ChartSer

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)

variable {S : Type} [CommRing S] {d n n' k : ℕ} (m : ℕ)

def jQ (b : Fin k → Q S d n) : Jet S (Fin k × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m :=
  jetMap (fun s => psTrunc m ((b s.1).1 s.2)) fun s => FBIdJet.psTrunc_mem_orig m _ ((b s.1).2 s.2)

theorem jQ_psJet (b : Fin k → Q S d n) (f : PS S k d) : jQ m b (psJet m f) = psJet m (sb b f) := by
  rw [sb_apply]; exact (FBIdJet.psJet_subst m (fun s : Fin k × Fin d => (b s.1).1 s.2) (fun s => (b s.1).2 s.2) f).symm

theorem jQ_X (b : Fin k → Q S d n) (s : Fin k × Fin d) :
    jQ m b (Ideal.Quotient.mk _ (MvPolynomial.X s)) = psJet m ((b s.1).1 s.2) := by
  rw [jQ, jetMap_mk, MvPolynomial.aeval_X]; rfl

theorem psJet_X {κ : Type} [Fintype κ] [DecidableEq κ] (s : κ) :
    psJet m (MvPowerSeries.X s : MvPowerSeries κ S) = Ideal.Quotient.mk _ (MvPolynomial.X s) := by
  rw [← MvPolynomial.coe_X, psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem psJet_zero {κ : Type} [Fintype κ] [DecidableEq κ] : psJet m (0 : MvPowerSeries κ S) = 0 := by
  first
    | simp [psJet, psTrunc]
    | (simp only [psJet, psTrunc]; simp)

theorem jQ_comp (b : Fin n → Q S d n') (a : Fin k → Q S d n) : (jQ m b).comp (jQ m a) = jQ m fun j => sq b (a j) :=
  jet_hom_ext fun s => by rw [AlgHom.comp_apply, jQ_X, jQ_X, jQ_psJet]; rfl

theorem subst_eq (φ : Fin k × Fin d → MvPolynomial (Fin n × Fin d) S) (a : Fin k → Q S d n)
    (h : ∀ s, Ideal.Quotient.mk _ (φ s) = psJet m ((a s.1).1 s.2)) (hc : ∀ s, MvPolynomial.constantCoeff (φ s) = 0) :
    jetSubstP m φ = jQ m a := jet_hom_ext fun s => by
  rw [jQ_X, ← h, jetSubstP, jetMap_mk, MvPolynomial.aeval_X, hc, map_zero, sub_zero]

theorem mk_psIn (r : Fin k → Fin n) (f : PS S k d) :
    Ideal.Quotient.mk _ (psIn d m r f) = psJet m (sb (fun i => (gen (r i) : Q S d n)) f) := by
  rw [← jQ_psJet, psIn, mk_rename]
  refine AlgHom.congr_fun (jet_hom_ext fun s => ?_) _
  rw [jQ_X, jetMap_mk, MvPolynomial.aeval_X]; exact (psJet_X m _).symm

theorem ps_ext {κ : Type} [Fintype κ] [DecidableEq κ] {f g : MvPowerSeries κ S} (h : ∀ m, psJet m f = psJet m g) : f = g :=
  Chart.pj_ext fun m => by
    have := h m
    rwa [psJet, psJet, FBIdJet.psTrunc_eq, FBIdJet.psTrunc_eq] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0} {x0 : Sp S ⟶ X0}
  (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

def PP (u : Q S d n) : jOG x0 d m n ⟶ t.G := homAt x0 (jQ m ![u]) ≫ x m

theorem PP_sq (b : Fin n → Q S d n') (u : Q S d n) : homAt x0 (jQ m b) ≫ PP m x u = PP m x (sq b u) := by
  rw [PP, PP, ← Category.assoc, homAt_comp, jQ_comp]
  exact congrArg (fun a => homAt x0 (jQ m a) ≫ x m) (funext fun j => by fin_cases j; rfl)

theorem PP_gen (i : Fin n) : jptG t x0 d x m i = PP m x (gen i) :=
  congrArg (fun g => homAt x0 g ≫ x m) (jet_hom_ext fun s => by
    obtain ⟨j, s⟩ := s
    obtain rfl := Subsingleton.elim j 0
    rw [jQ_X, jetCopy, jetMap_mk, MvPolynomial.aeval_X]; exact (psJet_X m _).symm)

def VV (y : (jOG x0 d m n).left) (f : PS S n d) : (jOG x0 d m n).left.presheaf.stalk y :=
  cst (𝟙 (Sp (Jet S (Fin n × Fin d) m))) y (psJet m f)

theorem VV_mul (y : (jOG x0 d m n).left) (f g : PS S n d) : VV m y (f * g) = VV m y f * VV m y g := by
  rw [VV, FBIdJet.psJet_mul, cst_mul]; rfl

theorem VV_one (y : (jOG x0 d m n).left) : VV m y (1 : PS S n d) = 1 := by rw [VV, FBIdJet.psJet_one, cst_one]

theorem VV_ext (hL : t.PP.L.IsLB) {f g : PS S n d}
    (h : ∀ m (y : (jOG x0 d m n).left) J, Good t.PP.L y J → VV m y f = VV m y g) : f = g :=
  ps_ext fun m => cst_ext fun y => by
    choose J hJ using fun ψ : (jOG x0 d m n).left ⟶ t.G.left => exists_chart hL (ψ y)
    exact h m y J hJ

variable {m} {y : (jOG x0 d m n).left} {J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L y J)

def ee (e : ∀ m, FrTyG t x0 d x m) (y : (jOG x0 d m n).left) (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι)
    (u v : Q S d n) : ((jOG x0 d m n).left.presheaf.stalk y)ˣ :=
  val (L := t.PP.L) (φ := cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (ε := cε 2) (e m)
    (homAt x0 (jQ m ![u, v])).left y J

include hJ in
theorem val_peG (e : ∀ m, FrTyG t x0 d x m) (b : Fin k → Q S d n) (φ : Fin 2 → Fin d → MvPolynomial (Fin k × Fin d) S)
    (p q : Q S d k) (h : ∀ s : Fin 2 × Fin d, Ideal.Quotient.mk _ (φ s.1 s.2) = psJet m (((![p, q] : Fin 2 → _) s.1).1 s.2))
    (hc : ∀ s : Fin 2 × Fin d, MvPolynomial.constantCoeff (φ s.1 s.2) = 0) :
    val (peG t x0 d x e m φ) (homAt x0 (jQ m b)).left y J = ee x e y J (sq b p) (sq b q) := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [subst_eq m _ _ h hc, ← Over.comp_left, homAt_comp, jQ_comp]
  exact congrArg (fun a => val (L := t.PP.L) (φ := cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)])
    (ε := cε 2) (e m) (homAt x0 (jQ m a)).left y J) (funext fun j => by fin_cases j <;> rfl)

include hJ in
theorem val_scale {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : (jOG x0 d m n).left ⟶ Y) :
    val (scaleGenG t φ ε u g) r y J = gm r y ⊤ u * val g r y J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r y le_top (hJ.mem φ r) u) rfl)

theorem gm_unit (u : (Jet S (Fin k × Fin d) m)ˣ) (b : Fin k → Q S d n) (f : PS S k d)
    (hf : (u : Jet S (Fin k × Fin d) m) = psJet m f) :
    (gm (homAt x0 (jQ m b)).left y ⊤ (unitΓ u)).val = VV m y (sb b f) := by
  rw [VV, ← jQ_psJet, ← hf]
  refine (gs_unit (homAt x0 (jQ m b)).left y ⊤ trivial (unitΓ u)).symm.trans
    (Eq.trans ?_ (cst_comp (𝟙 _) (jQ m b : Jet S (Fin k × Fin d) m →+* Jet S (Fin n × Fin d) m) y u.val))
  rw [Category.id_comp]; rfl

section Dict

variable {G : FGLaw S d} {A : Germ.OAct (𝓞 E) G} {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)}
  {uvec : κ → Fin d → S} {x} (hc : IsChartG t x0 d G.F A.act tg uvec x)

variable (G) in

abbrev FQ : Q S d 2 := ⟨G.F, G.const⟩

variable (A) in

abbrev AQ (a : 𝓞 E) : Q S d 1 := ⟨A.act a, A.const a⟩

include hc

theorem PP_op (u v : Q S d n) : PP m x (op (FQ G) u v) = PP m x u * PP m x v := by
  have e := hc.law m
  rw [subst_eq m _ ![FQ G] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl)
    (fun s => (cc_psTrunc m _).trans (G.const _)), PP_gen, PP_gen] at e
  have := congrArg (homAt x0 (jQ m ![u, v]) ≫ ·) e
  simp only [MonObj.comp_mul, PP_sq, sq_gen] at this
  exact (PP_sq m x _ _).symm.trans this

theorem PP_ac (a : 𝓞 E) (u : Q S d n) : PP m x (ac (AQ A a) u) = PP m x u ≫ t.act.act a := by
  have e := hc.act m a
  rw [subst_eq m _ ![AQ A a] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl)
    (fun s => (cc_psTrunc m _).trans (A.const _ _))] at e
  exact (PP_sq m x _ _).symm.trans ((congrArg (homAt x0 (jQ m ![u]) ≫ ·) e).symm.trans (Category.assoc _ _ _).symm)

theorem PP_zero : PP m x (0 : Q S d n) = 1 := by
  have e : jQ m ![(0 : Q S d n)] = (Algebra.ofId S _).comp (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) := jet_hom_ext fun s => by
    obtain ⟨j, s⟩ := s
    obtain rfl := Subsingleton.elim j 0
    rw [jQ_X, AlgHom.comp_apply]
    refine (psJet_zero m).trans (Eq.symm ?_)
    show Algebra.ofId S _ (MvPolynomial.aeval (fun _ => (0 : S)) (MvPolynomial.X _)) = _
    rw [MvPolynomial.aeval_X, map_zero]
  rw [PP, e, ← homAt_comp, Category.assoc, hc.zero m, MonObj.comp_one]

omit hc in
theorem hX (i : Fin k) (j : Fin d) : (Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) : Jet S (Fin k × Fin d) m) =
    psJet m ((gen i : Q S d k).1 j) := (psJet_X m _).symm

omit hc in
theorem hF (i i' : Fin k) (j : Fin d) : (Ideal.Quotient.mk _ (psIn d m ![i, i'] (G.F j)) : Jet S (Fin k × Fin d) m) =
    psJet m ((op (FQ G) (gen i) (gen i') : Q S d k).1 j) :=
  (mk_psIn m _ _).trans (congrArg (fun a => psJet m (sb a (G.F j))) (funext fun l => by fin_cases l <;> rfl))

omit hc in
theorem hA (a : 𝓞 E) (i : Fin k) (j : Fin d) : (Ideal.Quotient.mk _ (psIn d m ![i] (A.act a j)) : Jet S (Fin k × Fin d) m) =
    psJet m ((ac (AQ A a) (gen i) : Q S d k).1 j) :=
  (mk_psIn m _ _).trans (congrArg (fun b => psJet m (sb b (A.act a j))) (funext fun l => by fin_cases l; rfl))

omit hc

variable {e : ∀ m, FrTyG t x0 d x m} {ph1 ph2 : PS S 3 d} {sy : PS S 2 d} {ad : 𝓞 E → PS S 2 d}
  (hf : IsFrameG t x0 d x G.F A.act ph1 ph2 sy ad e)
include hJ

theorem peXX (b : Fin k → Q S d n) (i i' : Fin k) :
    val (peG t x0 d x e m ![fun j => MvPolynomial.X (i, j), fun j => MvPolynomial.X (i', j)]) (homAt x0 (jQ m b)).left y J =
      ee x e y J (b i) (b i') :=
  (val_peG x hJ e b _ (gen i) (gen i') (by rintro ⟨l, j⟩; fin_cases l <;> exact hX _ j)
    (by rintro ⟨l, j⟩; fin_cases l <;> exact MvPolynomial.constantCoeff_X _ _)).trans (by rw [sq_gen, sq_gen])

theorem val_th (b : Fin 3 → Q S d n) (i₀ i₁ i₂ : Fin 3) :
    val (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m i₀) (lift (jptG t x0 d x m i₁)
      (jptG t x0 d x m i₂))).left) (homAt x0 (jQ m b)).left y J =
      cubV t.cub y J (PP m x (b i₀)) (PP m x (b i₁)) (PP m x (b i₂)) :=
  (val_cub t.cub _ hJ _ _ _).trans (by simp only [PP_gen, PP_sq, sq_gen])

include hf

theorem frame_biext_dictionary_first_partial_law (u v w : Q S d n) : VV m y (E3 ph1 u v w) = (cubV t.cub y J (PP m x u) (PP m x v) (PP m x w) *
    (ee x e y J (op (FQ G) u v) w)⁻¹ * ee x e y J u w * ee x e y J v w).val := by
  obtain ⟨U, hU, h⟩ := hf.ph1 m
  have hc := gm_unit (y := y) U ![u, v, w]
  have e₀ := val_peG x hJ e ![u, v, w] ![fun j => psIn d m ![0, 1] (G.F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] (op (FQ G) (gen 0) (gen 1)) (gen 2)
    (by rintro ⟨l, j⟩; fin_cases l; exacts [hF 0 1 j, hX 2 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [(cc_psIn d m _ _).trans (G.const j), MvPolynomial.constantCoeff_X _ _])
  rw [sq_op, sq_gen, sq_gen, sq_gen] at e₀
  have k := (val_th hJ ![u, v, w] 0 1 2).symm.trans ((val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 0 2))) ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 1 2))))))))))
  refine (hc _ hU).symm.trans (congrArg Units.val (Additive.ofMul.injective ?_))
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul, ofMul_inv, Matrix.cons_val] at k' ⊢
  linear_combination (norm := abel) -k'

theorem frame_biext_dictionary_second_partial_law (u v w : Q S d n) : VV m y (E3 ph2 u v w) = (cubV t.cub y J (PP m x u) (PP m x v) (PP m x w) *
    (ee x e y J u (op (FQ G) v w))⁻¹ * ee x e y J u v * ee x e y J u w).val := by
  obtain ⟨U, hU, h⟩ := hf.ph2 m
  have hc := gm_unit (y := y) U ![u, v, w]
  have C := isCub_cubV t.cub hJ
  have e₀ := val_peG x hJ e ![u, v, w] ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (G.F j)] (gen 0) (op (FQ G) (gen 1) (gen 2))
    (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, hF 1 2 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, (cc_psIn d m _ _).trans (G.const j)])
  rw [sq_op, sq_gen, sq_gen, sq_gen] at e₀
  have k := (val_th hJ ![u, v, w] 1 2 0).symm.trans ((val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 0 1))) ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 0 2))))))))))
  rw [C.s12, C.s01] at k
  refine (hc _ hU).symm.trans (congrArg Units.val (Additive.ofMul.injective ?_))
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul, ofMul_inv, Matrix.cons_val] at k' ⊢
  linear_combination (norm := abel) -k'

theorem dict_sy (u v : Q S d n) : VV m y (E2 sy u v) = (ee x e y J v u * (ee x e y J u v)⁻¹).val := by
  obtain ⟨U, hU, h⟩ := hf.sy m
  have hc := gm_unit (y := y) U ![u, v]
  generalize hq : gm (homAt x0 (jQ m ![u, v])).left y ⊤ (unitΓ U) = c at hc
  have k : ee x e y J u v = c⁻¹ * ee x e y J v u := (val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·)
    (((congrArg _ (map_inv (Units.map (toΓ _).toMonoidHom) U)).trans (map_inv _ _)).trans (congrArg (·⁻¹) hq)) (peXX hJ _ 1 0)))
  refine (hc _ hU).symm.trans (congrArg Units.val ?_)
  rw [k, mul_inv, inv_inv, mul_comm c, mul_inv_cancel_left]

omit hf in
theorem dict_ad (a : 𝓞 E) {K : Type} [Fintype K] {φ : K → ((t.G ⊗ t.G).left ⟶ t.G.left)} {ε : K → ℤ}
    (wL : LB.Gen (LB.LinComb t.PP.L φ ε)) (U : (Jet S (Fin 2 × Fin d) m)ˣ) (hU : (U : Jet S (Fin 2 × Fin d) m) = psJet m (ad a))
    (h : LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _
      (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left)
      (peG t x0 d x e m ![fun j => psIn d m ![0] (A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)]))
      (scaleGenG t _ _ (unitΓ U) (peG t x0 d x e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (A.act (H.bar a) j)])))
    (u v : Q S d n) : VV m y (E2 (ad a) u v) = (val₂ wL y J (PP m x u) (PP m x v) * ee x e y J (ac (AQ A a) u) v *
      (ee x e y J u (ac (AQ A (H.bar a)) v))⁻¹).val := by
  have hc := gm_unit (y := y) U ![u, v]
  have e₀ := val_peG x hJ e ![u, v] ![fun j => psIn d m ![0] (A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)] (ac (AQ A a) (gen 0)) (gen 1)
    (by rintro ⟨l, j⟩; fin_cases l; exacts [hA a 0 j, hX 1 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [(cc_psIn d m _ _).trans (A.const _ j), MvPolynomial.constantCoeff_X _ _])
  have e₁ := val_peG x hJ e ![u, v] ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn d m ![1] (A.act (H.bar a) j)] (gen 0) (ac (AQ A (H.bar a)) (gen 1))
    (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, hA _ 1 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, (cc_psIn d m _ _).trans (A.const _ j)])
  rw [sq_ac, sq_gen, sq_gen] at e₀ e₁
  have e₂ := val_ros wL (homAt x0 (jQ m ![u, v])) hJ (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))
  simp only [PP_gen, PP_sq, sq_gen] at e₂
  have k := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (by simpa only [PP_gen] using e₂) e₀)).symm.trans
    ((val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl e₁)))
  exact (hc _ hU).symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

omit hf in
theorem dict_ax (ha : FrAxes t x0 d x e) (u : Q S d n) : ee x e y J 0 u = 1 ∧ ee x e y J u 0 = 1 := by
  have z : ∀ j, (Ideal.Quotient.mk _ 0 : Jet S (Fin 1 × Fin d) m) = psJet m ((0 : Q S d 1).1 j) := fun j =>
    (map_zero _).trans (psJet_zero m).symm
  have e₀ := val_peG x hJ e ![u] ![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] 0 (gen 0) (by rintro ⟨l, j⟩; fin_cases l; exacts [z j, hX 0 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [map_zero _, MvPolynomial.constantCoeff_X _ _])
  have e₁ := val_peG x hJ e ![u] ![fun j => MvPolynomial.X ((0 : Fin 1), j), fun _ => 0] (gen 0) 0 (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, z j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, map_zero _])
  rw [map_zero, sq_gen] at e₀ e₁
  exact ⟨e₀.symm.trans ((val_corr hJ (ha m).1 _).trans (val_one _)), e₁.symm.trans ((val_corr hJ (ha m).2 _).trans (val_one _))⟩

end Dict

section Law

variable {G : FGLaw S d} {A : Germ.OAct (𝓞 E) G}

theorem at₂ {p q : Q S d 2} (h : p.1 = q.1) (u v : Q S d n) : sq ![u, v] p = sq ![u, v] q := by rw [Subtype.ext h]

theorem opc (u v : Q S d n) : op (FQ G) u v = op (FQ G) v u := by
  have := at₂ (p := op (FQ G) (gen 1) (gen 0)) (q := FQ G) ((op_val _ _ _).trans (funext G.comm)) v u
  rw [sq_op, sq_gen, sq_gen] at this; exact this

theorem op0 (u : Q S d n) : op (FQ G) 0 u = u := by
  have := congrArg (sq ![u]) (show op (FQ G) 0 (gen 0) = (gen 0 : Q S d 1) from
    Subtype.ext ((op_val _ _ _).trans (funext G.unit)))
  rwa [sq_op, map_zero, sq_gen] at this

theorem opa (u v w : Q S d n) : op (FQ G) (op (FQ G) u v) w = op (FQ G) u (op (FQ G) v w) := by
  have := congrArg (sq ![u, v, w]) (show op (FQ G) (op (FQ G) (gen 0) (gen 1)) (gen 2) =
    op (FQ G) (gen 0) (op (FQ G) (gen 1) (gen 2 : Q S d 3)) from Subtype.ext (by
      simp only [op_val]; exact funext G.assoc))
  simp only [sq_op, sq_gen] at this; exact this

theorem ac0 (a : 𝓞 E) : ac (AQ A a) (0 : Q S d n) = 0 := Subtype.ext (funext fun i => by
  have e := TB.LogPf.ev_zeroFam (n := n) (A.act a i)
  rw [A.const a i, map_zero] at e
  exact ((sb_apply _ _).trans (congrArg (ev · (A.act a i)) (funext fun j => by fin_cases j; rfl))).trans e)

theorem ac_op (a : 𝓞 E) (u v : Q S d n) : ac (AQ A a) (op (FQ G) u v) = op (FQ G) (ac (AQ A a) u) (ac (AQ A a) v) := by
  have := at₂ (p := ac (AQ A a) (op (FQ G) (gen 0) (gen 1))) (q := op (FQ G) (ac (AQ A a) (gen 0)) (ac (AQ A a) (gen 1)))
    (by simp only [op_val, ac_val]; exact A.hom a) u v
  simp only [sq_op, sq_ac, sq_gen] at this; exact this

theorem ac_add (a b : 𝓞 E) (u : Q S d n) : ac (AQ A (a + b)) u = op (FQ G) (ac (AQ A a) u) (ac (AQ A b) u) :=
  (congrArg (sq ![u]) (show AQ A (a + b) = op (FQ G) (AQ A a) (AQ A b) from
    Subtype.ext ((A.add_act a b).trans (op_val (FQ G) (AQ A a) (AQ A b)).symm))).trans (sq_op _ _ _ _)

theorem ac_mul (a b : 𝓞 E) (u : Q S d n) : ac (AQ A (a * b)) u = ac (AQ A a) (ac (AQ A b) u) :=
  (congrArg (sq ![u]) (show AQ A (a * b) = ac (AQ A a) (AQ A b) from
    Subtype.ext ((A.mul_act a b).trans (ac_val (AQ A a) (AQ A b)).symm))).trans (sq_ac _ _ _)

theorem ac_one (u : Q S d n) : ac (AQ A 1) u = u :=
  (congrArg (sq ![u]) (show AQ A 1 = gen 0 from Subtype.ext A.one_act)).trans (sq_gen _ _)

end Law

set_option maxHeartbeats 4000000 in
theorem fbId : FBIdSt := by
  intro E _ _ _ H X0 t hPow _ hs S _ x0 d G A κ _ tg uvec x e ph1 ph2 sy ad hc hf ha had
  have hL := t.PP.isLB
  have hp := (hPow 3).2
  have := t.act.hom
  choose wL hw hU using hf.ad
  have hW : ∀ a {T : Over X0} (p q : T ⟶ t.G) (U : Type) [CommGroup U] (h : (T.left ⟶ t.G.left) → U),
      ∏ i, h ((lift p q).left ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) ^ Sum.elim (cε 2) (fun I => -cε 2 I) i =
      h (p * (q ≫ t.act.act (star a))).left * (h p.left)⁻¹ * (h (q ≫ t.act.act (star a)).left)⁻¹ *
        ((h ((p ≫ t.act.act a) * q).left)⁻¹ * h (p ≫ t.act.act a).left * h q.left) := fun a T p q U _ h => by
    refine (prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _
      (prod_cube₂ _ _ fun r => h ((lift p q).left ≫ r)) (prod_neg _ _ (prod_cube₂ _ _ fun r => h ((lift p q).left ≫ r)))).trans ?_
    simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, hs]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have dA : ∀ {n m} {y : (jOG x0 d m n).left} {J}, Good t.PP.L y J → ∀ a (u v : Q S d n), VV m y (E2 (ad a) u v) =
      (val₂ (wL a) y J (PP m x u) (PP m x v) * ee x e y J (ac (AQ A a) u) v * (ee x e y J u (ac (AQ A (star a)) v))⁻¹).val :=
    fun {n m y J} hJ a u v => by
      obtain ⟨U, h₁, h₂⟩ := hU a m
      rw [hs]; exact dict_ad hJ a (wL a) U h₁ h₂ u v
  have h1 : ∀ {n m} {y : (jOG x0 d m n).left} {J}, Good t.PP.L y J → ∀ a, val₂ (wL a) y J (1 : jOG x0 d m n ⟶ t.G) 1 = 1 :=
    fun {n m y J} hJ a => by
      have k := dA hJ a 0 0
      have z : E2 (ad a) (0 : Q S d n) 0 = 1 := by
        have e := TB.LogPf.ev_zeroFam (n := n) (ad a)
        rw [had, map_one] at e
        exact ((sb_apply _ _).trans (congrArg (ev · (ad a)) (funext fun j => by fin_cases j <;> rfl))).trans e
      rw [z, VV_one, ac0, ac0, mul_inv_cancel_right, PP_zero hc] at k
      exact Units.ext k.symm
  have g2 : ∀ f : PS S 2 d, ev (n := 2) ![pt S d 0, pt S d 1] f = f := fun f => (formalSeriesValueAtTwoPoints_eq_ev f (gen 0) (gen 1)).symm.trans (formalSeriesValueAtTwoPoints_genericPoints f)
  have g3 : ∀ f : PS S 3 d, ev (n := 3) ![pt S d 0, pt S d 1, pt S d 2] f = f := fun f =>
    (formalSeriesValueAtThreePoints_eq_ev f (gen 0) (gen 1) (gen 2)).symm.trans (formalSeriesValueAtThreePoints_genericPoints f)
  have op0' : ∀ {n} (u : Q S d n), op (FQ G) u 0 = u := fun u => by rw [opc, op0]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have : E3 ph1 (0 : Q S d 2) (gen 0) (gen 1) = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)

      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at ⊢
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E3 ph1 (gen 0 : Q S d 2) 0 (gen 1) = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)

      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at ⊢
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E3 ph1 (gen 0 : Q S d 2) (gen 1) 0 = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)

      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at ⊢
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E3 ph2 (0 : Q S d 2) (gen 0) (gen 1) = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)

      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at ⊢
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E3 ph2 (gen 0 : Q S d 2) 0 (gen 1) = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)

      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at ⊢
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E3 ph2 (gen 0 : Q S d 2) (gen 1) 0 = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)

      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at ⊢
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E2 sy (0 : Q S d 1) (gen 0) = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)

      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at ⊢
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E2 sy (gen 0 : Q S d 1) 0 = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)

      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at ⊢
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · exact had
  · intro a
    have : E2 (ad a) (0 : Q S d 1) (gen 0) = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (cubical_law_left t.cub hp t.act wL hw hW hJ (h1 hJ) a 1 1 (PP m x (gen 0)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      simp only [_root_.mul_one, MonObj.one_comp, C.face, ofMul_one] at f0
      linear_combination (norm := abel) -f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · intro a
    have : E2 (ad a) (gen 0 : Q S d 1) 0 = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (cubical_law_right t.cub hp t.act wL hw hW hJ (h1 hJ) a (PP m x (gen 0)) 1 1)
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      simp only [_root_.mul_one, MonObj.one_comp, C.face₂, ofMul_one] at f0
      linear_combination (norm := abel) -f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E3 ph1 (gen 0 : Q S d 4) (gen 1) (gen 3) * E3 ph1 (op (FQ G) (gen 0) (gen 1)) (gen 2) (gen 3) = E3 ph1 (gen 1) (gen 2) (gen 3) * E3 ph1 (gen 0) (op (FQ G) (gen 1) (gen 2)) (gen 3) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (C.coc (PP m x (gen 0)) (PP m x (gen 1)) (PP m x (gen 2)) (PP m x (gen 3)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E3 ph1 (gen 1) (gen 0 : Q S d 3) (gen 2) = E3 ph1 (gen 0) (gen 1) (gen 2) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (C.s01 (PP m x (gen 1)) (PP m x (gen 0)) (PP m x (gen 2)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      rw [opc (gen 1)]
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero, g3] using this
  · have : E3 ph2 (gen 0 : Q S d 4) (gen 1) (gen 2) * E3 ph2 (gen 0) (op (FQ G) (gen 1) (gen 2)) (gen 3) = E3 ph2 (gen 0) (gen 2) (gen 3) * E3 ph2 (gen 0) (gen 1) (op (FQ G) (gen 2) (gen 3)) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (C.coc (PP m x (gen 1)) (PP m x (gen 2)) (PP m x (gen 3)) (PP m x (gen 0)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      simp only [C.s12 _ _ (PP m x (gen 0)), C.s01 _ (PP m x (gen 0))] at f0
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E3 ph2 (gen 0 : Q S d 3) (gen 2) (gen 1) = E3 ph2 (gen 0) (gen 1) (gen 2) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (C.s12 (PP m x (gen 0)) (PP m x (gen 2)) (PP m x (gen 1)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      rw [opc (gen 2)]
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero, g3] using this
  · have : E3 ph1 (gen 0 : Q S d 4) (gen 1) (gen 2) * E3 ph1 (gen 0) (gen 1) (gen 3) * E3 ph2 (op (FQ G) (gen 0) (gen 1)) (gen 2) (gen 3) = E3 ph2 (gen 0) (gen 2) (gen 3) * E3 ph2 (gen 1) (gen 2) (gen 3) * E3 ph1 (gen 0) (gen 1) (op (FQ G) (gen 2) (gen 3)) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (C.compat (PP m x (gen 0)) (PP m x (gen 1)) (PP m x (gen 2)) (PP m x (gen 3)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E2 sy (gen 0 : Q S d 2) (gen 1) * E2 sy (gen 1) (gen 0) = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)

      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at ⊢
      abel
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero, g2] using this
  · have : E3 ph2 (gen 0 : Q S d 3) (gen 1) (gen 2) * E2 sy (gen 0) (gen 1) * E2 sy (gen 0) (gen 2) = E2 sy (gen 0) (op (FQ G) (gen 1) (gen 2)) * E3 ph1 (gen 1) (gen 2) (gen 0) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul ((C.s01 (PP m x (gen 0)) (PP m x (gen 1)) (PP m x (gen 2))).trans (C.s12 _ _ _))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero, g3] using this
  · intro a
    have : E3 ph1 (ac (AQ A a) (gen 0 : Q S d 3)) (ac (AQ A a) (gen 1)) (gen 2) * E2 (ad a) (op (FQ G) (gen 0) (gen 1)) (gen 2) = E2 (ad a) (gen 0) (gen 2) * E2 (ad a) (gen 1) (gen 2) * E3 ph1 (gen 0) (gen 1) (ac (AQ A (star a)) (gen 2)) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (cubical_law_left t.cub hp t.act wL hw hW hJ (h1 hJ) a (PP m x (gen 0)) (PP m x (gen 1)) (PP m x (gen 2)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · intro a
    have : E3 ph2 (ac (AQ A a) (gen 0 : Q S d 3)) (gen 1) (gen 2) * E2 (ad a) (gen 0) (op (FQ G) (gen 1) (gen 2)) = E2 (ad a) (gen 0) (gen 1) * E2 (ad a) (gen 0) (gen 2) * E3 ph2 (gen 0) (ac (AQ A (star a)) (gen 1)) (ac (AQ A (star a)) (gen 2)) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (cubical_law_right t.cub hp t.act wL hw hW hJ (h1 hJ) a (PP m x (gen 0)) (PP m x (gen 1)) (PP m x (gen 2)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero] using this
  · have : E2 (ad 1) (gen 0 : Q S d 2) (gen 1) = 1 := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (adv_one t.cub hp t.act wL hw hW hJ (h1 hJ) (PP m x (gen 0)) (PP m x (gen 1)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero, g2] using this
  · intro a b
    have : E2 (ad (a * b)) (gen 0 : Q S d 2) (gen 1) = E2 (ad a) (ac (AQ A b) (gen 0)) (gen 1) * E2 (ad b) (gen 0) (ac (AQ A (star a)) (gen 1)) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (adv_mul t.cub hp t.act wL hw hW hJ (h1 hJ) a b (PP m x (gen 0)) (PP m x (gen 0)) (PP m x (gen 1)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero, g2] using this
  · intro a b
    have : E3 ph1 (ac (AQ A a) (gen 0 : Q S d 2)) (ac (AQ A b) (gen 0)) (gen 1) * E2 (ad (a + b)) (gen 0) (gen 1) = E2 (ad a) (gen 0) (gen 1) * E2 (ad b) (gen 0) (gen 1) * E3 ph2 (gen 0) (ac (AQ A (star a)) (gen 1)) (ac (AQ A (star b)) (gen 1)) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (adv_add t.cub hp t.act wL hw hW hJ (h1 hJ) a b (PP m x (gen 0)) (PP m x (gen 0)) (PP m x (gen 1)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero, g2] using this
  · intro a
    have : E2 (ad a) (gen 0 : Q S d 2) (gen 1) * E2 (ad (star a)) (gen 1) (gen 0) * E2 sy (ac (AQ A a) (gen 0)) (gen 1) = E2 sy (gen 0) (ac (AQ A (star a)) (gen 1)) := VV_ext hL fun m y J hJ => by
      have C := isCub_cubV t.cub (T := jOG x0 d m _) hJ
      simp only [VV_mul, VV_one, frame_biext_dictionary_first_partial_law hJ hf, frame_biext_dictionary_second_partial_law hJ hf, dict_sy hJ hf, dA hJ, ← Units.val_mul]
      refine (congrArg Units.val (Additive.ofMul.injective ?_)).trans (by first | exact Units.val_one | rfl)
      have f0 := congrArg Additive.ofMul (adv_sy t.cub hp t.act wL hw hW hJ (h1 hJ) a (PP m x (gen 0)) (PP m x (gen 0)) (PP m x (gen 1)))
      simp only [PP_op hc, PP_ac hc, PP_zero hc, op0, op0', opa, ac0, ac_op, ac_add, ac_one, star_add, star_one, star_star, star_mul, ac_mul, (dict_ax hJ ha _).1, (dict_ax hJ ha _).2, C.face, C.face₂, C.face₃, ofMul_mul,
        ofMul_inv, ofMul_one] at f0 ⊢
      linear_combination (norm := abel) f0
    simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val, ZeroMemClass.coe_zero, g2] using this

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd
