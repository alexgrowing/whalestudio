import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods

set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer

section Tay

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {R : Type} [CommRing R] [Algebra ℂ R]

abbrev evT {W : Opens E} (R : Type) [CommRing R] [Algebra ℂ R] (p : E) (hp : p ∈ W) : R ⊗[ℂ] Hol W →ₐ[ℂ] R :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ R) ((Algebra.ofId ℂ R).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)

def IsTay {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} (N : ℕ) (t : I → R) {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀) : Prop :=
  ∀ (h : Hol W) (p : Tot Empty g) (hp : p ∈ W₀), evT R p hp (ρ h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)

end Tay

namespace Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {R : Type} [CommRing R]

def shA {l : Λ} {k k' : K.K} (h : K.le l k' k) : Hol (K.W k) →ₐ[ℂ] Hol (K.W k') :=
  Hol.comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)

theorem shA_apply {l : Λ} {k k' : K.K} (h : K.le l k' k) (x : Hol (K.W k)) : shA h x = sh h x := rfl

variable (K) in

structure DObj (η : Hol F.V →+* R) (M : Ideal R) : Type 1 where

  T : K.Obj
  [alg : Algebra R T.C]
  compat : ∀ f, algebraMap (Hol F.V) T.C f = algebraMap R T.C (η f)
  mem : ∀ d ∈ M, algebraMap R T.C d ∈ T.J

attribute [instance] DObj.alg

variable {η : Hol F.V →+* R} {M : Ideal R}

instance : Category (K.DObj η M) where
  Hom S S' := {f : S.T ⟶ S'.T // ∀ d, f.φ (algebraMap R S.T.C d) = algebraMap R S'.T.C d}
  id S := ⟨𝟙 _, fun _ ↦ rfl⟩
  comp f f' := ⟨f.1 ≫ f'.1, fun d ↦ by rw [comp_φ, f.2, f'.2]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f f' f'' := Subtype.ext (Category.assoc _ _ _)

variable (K η M) in

@[reducible] def OD : K.DObj η M ⥤ CommAlgCat.{0} R where
  obj S := CommAlgCat.of _ S.T.C
  map f := CommAlgCat.ofHom { (f.1.φ : _ →+* _) with commutes' := f.2 }

variable (K η M) in

def perZD (q : Λ →+ R) : Z1 (K.OD η M) :=
  ⟨fun _ S' f ↦ algebraMap R S'.T.C (q f.1.deg), fun S S' S'' f f' ↦ by
    change algebraMap _ S''.T.C (q (f.1.deg + f'.1.deg)) = f'.1.φ (algebraMap _ _ _) + algebraMap _ S''.T.C _
    rw [f'.2, map_add, map_add]⟩

variable (K η M) in

def perClD (q : Λ →+ R) : CatCoh.H1 (K.OD η M) := H1.mk _ (K.perZD η M q)

variable (K η M) in

def forgetD : CoefMap η K.Oc (K.OD η M) where
  G := { obj S := S.T, map f := f.1 }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S r b := by
    change r • (b : S.T.C) = η r • (b : S.T.C)
    rw [Algebra.smul_def, Algebra.smul_def, S.compat]

theorem forgetD_perCl (per : Λ →+ Hol F.V) :
    (K.forgetD η M).pull1 (K.perCl per) = K.perClD η M (η.toAddMonoidHom.comp per) :=
  congrArg (H1.mk _) (Subtype.ext (funext fun _ ↦ funext fun S' ↦ funext fun f ↦ S'.compat (per f.1.deg)))

end Charts

section Theta

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {R : Type} [CommRing R] {η : Hol F.V →+* R} {M : Ideal R}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}
  {D : Type} [CommRing D] {J : Ideal D}

structure IsOver (η : Hol F.V →+* R) (M : Ideal R) (s : X ⟶ Sp B) (σ : B →+* Hol F.V) (J : Ideal D) (s' : X ⟶ Sp D)
    (π : D →+* B) (ι : D →+* R) : Prop where
  w : s' = s ≫ spMap π
  mem : ∀ d ∈ J, ι d ∈ M
  red : ∀ d, ι d - η (σ (π d)) ∈ M

variable (r : Real K s σ) (κ : DividedPowers J) {s' : X ⟶ Sp D} {π : D →+* B} {ι : D →+* R} (H : IsOver η M s σ J s' π ι)

def Real.objD (S : K.DObj η M) : Thick κ s' where
  B := S.T.C
  alg := ((algebraMap R S.T.C).comp ι).toAlgebra
  J := S.T.J
  δ := S.T.δ
  nil := letI := S.T.ratAlg; isPDNilpotent_of_rat _ S.T.nil
  dp := letI := S.T.ratAlg; isDPMorphism_of_rat κ S.T.δ _ fun d hd ↦ S.mem _ (H.mem d hd)
  B₀ := S.T.C ⧸ S.T.J
  π := Ideal.Quotient.mk S.T.J
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap ((Ideal.Quotient.mk S.T.J).comp S.T.ρ) ≫ r.x S.T.k
  w := by
    rw [H.w, Category.assoc, ← Category.assoc (r.x _), r.w, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    refine RingHom.ext fun d ↦ (Ideal.Quotient.eq.2 ?_).symm
    have := S.mem _ (H.red d)
    rw [map_sub, ← S.compat, ← S.T.ρ_cst] at this
    exact this

def Real.coefD : CoefMap ι (O κ s') (K.OD η M) where
  G :=
    { obj := r.objD κ H
      map {S S'} f :=
        { φ := { (f.1.φ : S.T.C →+* S'.T.C) with commutes' := fun d ↦ f.2 (ι d) }
          φ₀ := Ideal.quotientMap S'.T.J (f.1.φ : S.T.C →+* S'.T.C) f.1.mem
          comm := fun _ ↦ rfl
          dp := letI := S'.T.ratAlg; isDPMorphism_of_rat S.T.δ S'.T.δ (f.1.φ : S.T.C →+* S'.T.C) f.1.mem
          pt := r.analyticChartsRealization_comp_point_eq f.1 } }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S d c := (Algebra.smul_def (A := S.T.C) (ι d) c).symm

end Theta

section Inhabitants

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

def jetAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} (v p : E) (hp : p ∈ W) :
    Hol W →+* DualNumber ℂ where
  toFun h := TrivSqZeroExt.inl (Hol.ev p hp h) + TrivSqZeroExt.inr (Hol.ev p hp (Hol.der v h))
  map_one' := by simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [Derivation.leibniz, mul_comm]
  map_zero' := by simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

def Charts.dualD (K : Charts F) (k : K.K) (v : I → ℂ) (p : Tot I g) (hp : p ∈ K.W k) :
    K.DObj (jetAt v p.1 (K.base k p hp)) (Ideal.span {DualNumber.eps}) where
  T :=
    { k := k
      C := DualNumber ℂ
      alg := (jetAt v p.1 (K.base k p hp)).toAlgebra
      J := Ideal.span {DualNumber.eps}
      nil := ⟨2, by rw [Ideal.span_singleton_pow, sq, DualNumber.eps_mul_eps]; simp⟩
      ρ := jetAt ((v, 0) : Tot I g) p hp
      ρ_cst := fun f ↦ by
        have e1 : Hol.ev p hp (K.cst k f) = Hol.ev p.1 (K.base k p hp) f := by
          rw [Hol.ev_apply, Hol.ev_apply, K.fn_cst k f hp]
        have e2 : Hol.ev p hp (Hol.der ((v, 0) : Tot I g) (K.cst k f)) =
            Hol.ev p.1 (K.base k p hp) (Hol.der v f) := by
          rw [Hol.ev_apply, Hol.ev_apply, Hol.fn_der _ _ (K.base k p hp)]
          refine (Hol.fn_der_comap _ _ _ _ f hp).trans ?_
          rw [fderiv_fst]; rfl
        change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : DualNumber ℂ) = TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _
        rw [e1, e2] }
  alg := Algebra.id (DualNumber ℂ)
  compat _ := rfl
  mem _ h := h

theorem Charts.dualD_J_ne_bot (K : Charts F) (k : K.K) (v : I → ℂ) (p : Tot I g) (hp : p ∈ K.W k) :
    (K.dualD k v p hp).T.J ≠ ⊥ := by
  intro h
  have h' : (DualNumber.eps : DualNumber ℂ) = 0 := Ideal.span_singleton_eq_bot.1 h
  simpa using congrArg TrivSqZeroExt.snd h'

theorem isOver_dual (v z : I → ℂ) (hz : z ∈ F.V) {X : Scheme.{0}} (s : X ⟶ Sp ℂ) :
    IsOver (F := F) (jetAt v z hz) (Ideal.span {DualNumber.eps}) s (algebraMap ℂ (Hol F.V))
      (Ideal.span {DualNumber.eps}) (s ≫ spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom (RingHom.id (DualNumber ℂ)) where
  w := rfl
  mem _ h := h
  red d := by
    refine Ideal.mem_span_singleton'.2 ⟨TrivSqZeroExt.inl d.snd, ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [jetAt]

def Charts.Obj.toD {K : Charts F} (T : K.Obj) : K.DObj (RingHom.id _) ⊥ where
  T := T
  alg := T.alg
  compat _ := rfl
  mem d h := by rw [Ideal.mem_bot.1 h, map_zero]; exact T.J.zero_mem

example : ∃ (S S' : ellFam.allCharts.DObj (RingHom.id _) ⊥) (f : S ⟶ S'), S'.T.J ≠ ⊥ ∧ f.1.deg = (0, 1) :=
  ⟨Charts.Obj.toD _, Charts.Obj.toD _, ⟨ellFam.transl (0, 1) ≫
      ellFam.allCharts.tangentHom ellFam.totChart 0 (fun _ ↦ Complex.I, 0) ellFam_nontrivial.1,
        fun d ↦ AlgHom.commutes _ d⟩,
    Charts.dualAt_J_ne_bot _ _ _ _, add_zero _⟩

example : ∃ (η : Hol ellFam.V →+* DualNumber ℂ) (S : ellFam.allCharts.DObj η (Ideal.span {DualNumber.eps})),
    S.T.J ≠ ⊥ :=
  ⟨_, ellFam.allCharts.dualD ellFam.totChart (fun _ ↦ 1) (fun _ ↦ Complex.I, 0) ellFam_nontrivial.1,
    Charts.dualD_J_ne_bot _ _ _ _ _⟩

def resFib {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)} (hW : ∀ p ∈ W₀, ((0 : I → ℂ), p.2) ∈ W) :
    Hol W →ₐ[ℂ] Hol W₀ :=
  Hol.comap (fun p ↦ (0, p.2)) (fun _ _ ↦ analyticAt_const.prod analyticAt_snd) hW

def tay1 {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)} (hW : ∀ p ∈ W₀, ((0 : I → ℂ), p.2) ∈ W) (v : I → ℂ) :
    Hol W →+* DualNumber ℂ ⊗[ℂ] Hol W₀ where
  toFun h := 1 ⊗ₜ resFib hW h + DualNumber.eps ⊗ₜ resFib hW (Hol.der (v, 0) h)
  map_one' := by simp [Algebra.TensorProduct.one_def]
  map_mul' x y := by
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, tmul_add, add_mul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, DualNumber.eps_mul_eps, zero_tmul, add_zero]
    rw [mul_comm (resFib hW y)]; abel
  map_zero' := by simp
  map_add' x y := by simp only [map_add, tmul_add]; abel

theorem isTaylorExpansion_orderOne [DecidableEq I] {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, ((0 : I → ℂ), p.2) ∈ W) (v : I → ℂ) :
    IsTay 1 (fun i ↦ v i • (DualNumber.eps : DualNumber ℂ)) (tay1 hW v) := by
  intro h p hp
  have hd : HasFDerivAt (fun z : I → ℂ ↦ h.fn (z, p.2))
      ((fderiv ℂ h.fn (0, p.2)).comp (ContinuousLinearMap.inl ℂ _ _)) 0 :=
    HasFDerivAt.comp (𝕜 := ℂ) (g := h.fn) (f := fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) (0 : I → ℂ)
      (h.analytic _ (hW p hp)).differentiableAt.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℂ) (0 : I → ℂ) p.2)
  have e1 : Hol.ev p hp (resFib hW h) = h.fn (0, p.2) := by rw [Hol.ev_apply]; exact Hol.fn_comap _ _ _ _ hp
  have e2 : Hol.ev p hp (resFib hW (Hol.der (v, 0) h)) =
      ∑ i, v i * fderiv ℂ h.fn (0, p.2) (Pi.single i 1, 0) := by
    rw [Hol.ev_apply]
    refine (Hol.fn_comap _ _ _ _ hp).trans ((Hol.fn_der _ _ (hW p hp)).trans ?_)
    have : ((v, 0) : Tot I g) = ∑ i, v i • ((Pi.single i 1, 0) : Tot I g) := by
      ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum]; simp only [map_smul, smul_eq_mul]
  change evT _ p hp (_ + _) = _
  rw [map_add, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
    AlgHom.comp_apply, e1, e2]
  unfold GlobalTheory.PeriodFamily.taylor
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  congr 1
  · simp [Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one]
  · rw [← (Equiv.funUnique (Fin 1) I).symm.sum_comp]
    simp [iteratedFDeriv_one_apply, hd.fderiv, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, Finset.sum_smul,
      smul_smul, mul_comm, Finset.mul_sum]

end Inhabitants

end GlobalTheory.AnPer
