import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.PureCancel

noncomputable section

namespace PositivityTheory.ThKG.Loc.Cone.Fin

open scoped TensorProduct NNReal Matrix nonZeroDivisors GlobalTheory.VacAny Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LatVac
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}

variable (F) in

def rk (p : Fin n → E) (q : Fin d → E) : Matrix (Fin n) (Fin d) (AE F E) := Matrix.vecMulVec (GlobalTheory.ThK.incV F p) (GlobalTheory.ThK.incV F q)

variable (σ) in

abbrev hh (X : Spc F E n) (W : Spc F E d) (x y : Matrix (Fin n) (Fin d) (AE F E)) : AE F E :=
  hTens (cA σ) (incM F X.J) (incM F W.J) x y

variable {X : Spc F E n} {W : Spc F E d}

theorem hh_add (x x' y : Matrix (Fin n) (Fin d) (AE F E)) : hh σ X W (x + x') y = hh σ X W x y + hh σ X W x' y := by
  simp only [hh, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem hh_smul (a b : AE F E) (x y : Matrix (Fin n) (Fin d) (AE F E)) :
    hh σ X W (a • x) (b • y) = a * cA σ b * hh σ X W x y := by
  simp only [hh, hTens, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem hh_rk (p p' : Fin n → E) (q q' : Fin d → E) :
    hh σ X W (rk F p q) (rk F p' q') = inclR (F := F) (AF F) (form σ X.J p p' * form σ W.J q q') := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun _ => rfl
  have f1 : form σ X.J p p' = ∑ i, ∑ k, p i * (X.J i k * σ (p' k)) := by
    simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum]
  have f2 : form σ W.J q q' = ∑ i, ∑ k, q i * (W.J i k * σ (q' k)) := by
    simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [f1, f2, Finset.sum_mul_sum]
  simp only [Finset.sum_mul_sum, map_sum, hh, hTens, rk, Matrix.vecMulVec_apply, GlobalTheory.ThK.incV, incM, Matrix.map_apply, map_mul, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem incM_rk (p : Fin n → E) (q : Fin d → E) : incM F (Matrix.vecMulVec p q) = rk F p q := by
  ext i j; simp [incM, rk, GlobalTheory.ThK.incV, Matrix.vecMulVec_apply]

theorem rk_smul (s t : E) (p : Fin n → E) (q : Fin d → E) :
    rk F (s • p) (t • q) = inclR (F := F) (AF F) (s * t) • rk F p q := by
  ext i j
  simp only [rk, GlobalTheory.ThK.incV, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply]
  ring

theorem comp_lat {p p' : Fin n → E} {q q' : Fin d → E}
    (hp : ∀ x ∈ X.L, ∃ s : E, s • p' ∈ X.L ∧ form σ X.J x p = s * form σ X.J p' p)
    (hq : ∀ y ∈ W.L, ∃ t : E, t • q' ∈ W.L ∧ form σ W.J y q = t * form σ W.J q' q) (v : Pl F) {γ} (hγ : γ ∈ latAtV X W v) :
    ∃ t : AE F E, t • rk F p' q' ∈ latAtV X W v ∧ hh σ X W γ (rk F p q) = t * hh σ X W (rk F p' q') (rk F p q) := by
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
    obtain ⟨s, hs, hs'⟩ := hp x hx
    obtain ⟨t, ht, ht'⟩ := hq y hy
    refine ⟨algebraMap (AF F) (AE F E) a * inclR (F := F) (AF F) (s * t), AddSubgroup.subset_closure
      ⟨a, ha, hav, _, hs, _, ht, by rw [incM_rk, rk_smul, mul_smul, algebraMap_smul]⟩, ?_⟩
    have := hh_smul (σ := σ) (X := X) (W := W) (algebraMap (AF F) (AE F E) a) 1 (rk F x y) (rk F p q)
    rw [one_smul, algebraMap_smul, map_one, mul_one] at this
    rw [incM_rk, this, hh_rk, hh_rk, hs', ht']
    simp only [map_mul]; ring
  | zero => exact ⟨0, by rw [zero_smul]; exact zero_mem _, by simp [hh, hTens]⟩
  | add y z _ _ hy hz =>
    obtain ⟨t, h1, h2⟩ := hy
    obtain ⟨t', h1', h2'⟩ := hz
    exact ⟨t + t', by rw [add_smul]; exact add_mem h1 h1', by rw [hh_add, h2, h2', add_mul]⟩
  | neg y _ hy =>
    obtain ⟨t, h1, h2⟩ := hy
    refine ⟨-t, by rw [neg_smul]; exact neg_mem h1, ?_⟩
    have := hh_smul (σ := σ) (X := X) (W := W) (-1) 1 y (rk F p q)
    rw [one_smul, neg_one_smul, map_one, mul_one] at this
    rw [this, h2]; ring

theorem form_lin (J : Matrix (Fin n) (Fin n) E) (s t : E) (x u y z : Fin n → E) :
    form σ J (s • x + u + t • y) z = s * form σ J x z + form σ J u z + t * form σ J y z := by
  simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem exists_smul_y_mem_and_form_eq_of_isAdapted {B : Base F E} {m : ℕ} {Y₁ : Spc F E m} {H : Plane E n m} {i j : ℕ} (h : H.IsAdapted σ B X Y₁ i j) :
    ∀ z ∈ X.L, ∃ s : E, s • H.y ∈ X.L ∧ form σ X.J z H.x = s * form σ X.J H.y H.x := fun z hz => by
  obtain ⟨s, t, u, -, ht, -, rfl⟩ := h.split z hz
  exact ⟨t, ht, by rw [form_lin, h.xx, (h.orth u).1]; ring⟩

theorem plane_y {B : Base F E} {m : ℕ} {Y₁ : Spc F E m} {H : Plane E n m} {i j : ℕ} (h : H.IsAdapted σ B X Y₁ i j) :
    ∀ z ∈ X.L, ∃ s : E, s • H.x ∈ X.L ∧ form σ X.J z H.y = s * form σ X.J H.x H.y := fun z hz => by
  obtain ⟨s, t, u, hs, -, -, rfl⟩ := h.split z hz
  exact ⟨s, hs, by rw [form_lin, h.yy, (h.orth u).2]; ring⟩

variable {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem dirs {B : Base F E} {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e u}
    (h : Cfg B M M₁ H H' e u) : ∃ (V₀ V₁ : Matrix (Fin n) (Fin d) (AE F E)) (c : AE F E →ₐ[AF F] AE F E),
      (∀ l, u l = c l.1 • V₀) ∧ hh σ X W V₀ V₀ = 0 ∧ hh σ X W V₁ V₁ = 0 ∧
      (∀ t : AE F E, ∀ Φ ∈ schA F _, e (M.co.rho B.ψ (t • V₁) Φ) = e Φ) ∧
      ∀ v, ∀ γ ∈ latAtV X W v, ∃ t : AE F E, t • V₁ ∈ latAtV X W v ∧ hh σ X W γ V₀ = t * hh σ X W V₁ V₀ := by
  obtain ⟨i, j, hH⟩ := h.hH
  obtain ⟨i', j', hH'⟩ := h.hH'
  rcases h.ev with ⟨he, rfl⟩ | ⟨he, rfl⟩
  · refine ⟨rk F H.x H'.y, rk F H.y H'.x, AlgHom.id _ _, fun _ => rfl, by rw [hh_rk, hH.xx, zero_mul, map_zero],
      by rw [hh_rk, hH.yy, zero_mul, map_zero], fun t => he.inv _ (Or.inl ⟨t • GlobalTheory.ThK.incV F H.y, ?_⟩),
      fun v γ hγ => comp_lat (exists_smul_y_mem_and_form_eq_of_isAdapted hH) (plane_y hH') v hγ⟩
    ext a b; simp [rk, Matrix.vecMulVec_apply, mul_assoc]
  · refine ⟨rk F H.y H'.x, rk F H.x H'.y, cA σ, fun _ => rfl, by rw [hh_rk, hH.yy, zero_mul, map_zero],
      by rw [hh_rk, hH.xx, zero_mul, map_zero], fun t => he.inv _ (Or.inl ⟨t • GlobalTheory.ThK.incV F H'.y, ?_⟩),
      fun v γ hγ => comp_lat (plane_y hH) (exists_smul_y_mem_and_form_eq_of_isAdapted hH') v hγ⟩
    ext a b; simp [rk, Matrix.vecMulVec_apply, mul_left_comm]

end PositivityTheory.ThKG.Loc.Cone.Fin

end
