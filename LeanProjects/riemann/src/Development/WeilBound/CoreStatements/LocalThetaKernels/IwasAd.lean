import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt

noncomputable section

namespace PositivityTheory.ThKH.Iwas

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

def sg (v : Pl F) : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

theorem ev_sg (a : Fv F v) : evFin F v (sg v a) = a := evalV_singleFin_self v a

theorem mul_sg (u : AF F) (a : Fv F v) : u * sg v a = sg v (evFin F v u * a) := by
  refine Prod.ext (mul_zero _) (af_ext fun t => ?_)
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t (u.2 * singleFin v a) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F t (singleFin v _)
  by_cases ht : t = v
  · subst ht
    rw [map_mul, evalV_singleFin_self, evalV_singleFin_self]; rfl
  · rw [map_mul, evalV_singleFin_ne ht, evalV_singleFin_ne ht, mul_zero]

theorem at_sg (a : Fv F v) : At (evFin F v) (sg v a) := fun u hu => by
  rw [smul_eq_mul, mul_sg, hu, zero_mul, map_zero]

variable (E) in

def sgE (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := TensorProduct.map (sg v) LinearMap.id

omit [NumberField E] in
theorem comp_sgE (y : Fv F v ⊗[F] E) : compFin F E v (sgE E v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (· ⊗ₜ[F] x) (ev_sg a)
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem at_sgE (y : Fv F v ⊗[F] E) : At (evFin F v) (sgE E v y) := fun u hu => by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change (u • sg v a) ⊗ₜ[F] x = 0
    rw [at_sg a u hu, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

omit [NumberField E] in
theorem sgE_comp (z : AE F E) : sgE E v (compFin F E v z) = sg v 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change sg v (evFin F v a) ⊗ₜ[F] x = (sg v 1 * a) ⊗ₜ[F] x
    rw [mul_comm, mul_sg, mul_one]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

omit [NumberField E] in
theorem eq_zero_of_at {z : AE F E} (hz : At (evFin F v) z) (h : compFin F E v z = 0) : z = 0 := by
  have h1 := hz (1 - sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])
  rw [sub_smul, one_smul, ← sgE_comp, h, map_zero, sub_zero] at h1
  exact h1

def piE (h : w.under (𝓞 F) = v) : AE F E →+* w.adicCompletion E := (toCompl h).comp (compFin F E v)

theorem piE_incl (h : w.under (𝓞 F) = v) (x : E) : piE h (inclR (F := F) (AF F) x) = algebraMap E _ x := by
  change toCompl h (evFin F v 1 ⊗ₜ[F] x) = _
  rw [map_one, toCompl_tmul, map_one, one_mul]

theorem piE_cA {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) (z : AE F E) :
    piE h (cA σ z) = c (piE h z) := by
  change toCompl h _ = c (toCompl h _)
  rw [hc]
  congr 1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

section Vec

variable {ι : Type}

theorem vec_inj (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {y y' : ι → AE F E} (hy : At (evFin F v) (y - y'))
    (e : piE h ∘ y = piE h ∘ y') : y = y' := funext fun i => sub_eq_zero.1 <|
  eq_zero_of_at (fun u hu => congrFun (hy u hu) i) ((toCompl_bijective hw h).1 (by
    change piE h (y i - y' i) = _
    rw [map_sub, map_zero, sub_eq_zero]; exact congrFun e i))

theorem vec_surj (h : w.under (𝓞 F) = v) (z : ι → w.adicCompletion E) :
    ∃ y : ι → AE F E, At (evFin F v) y ∧ piE h ∘ y = z := by
  choose x hx using fun i => toCompl_surjective h (z i)
  exact ⟨fun i => sgE E v (x i), fun u hu => funext fun i => at_sgE _ u hu, funext fun i => by
    change toCompl h (compFin F E v (sgE E v (x i))) = _
    rw [comp_sgE, hx]⟩

end Vec

section Mat

variable {ι κ μ : Type}

theorem mat_inj (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {M M' : Matrix ι κ (AE F E)} (hM : At (evFin F v) (M - M'))
    (e : M.map (piE h) = M'.map (piE h)) : M = M' := funext fun i =>
  vec_inj hw h (fun u hu => congrFun (hM u hu) i) (congrFun e i)

theorem mat_surj (h : w.under (𝓞 F) = v) (N : Matrix ι κ (w.adicCompletion E)) :
    ∃ M : Matrix ι κ (AE F E), At (evFin F v) M ∧ M.map (piE h) = N := by
  choose M h1 h2 using fun i => vec_surj h (N i)
  exact ⟨Matrix.of M, fun u hu => funext fun i => h1 i u hu, funext h2⟩

omit [NumberField E] in
theorem at_sub {X : Type} [AddCommGroup X] [Module (AF F) X] {x y : X} (hx : At (evFin F v) x) (hy : At (evFin F v) y) :
    At (evFin F v) (x - y) := fun u hu => by rw [smul_sub, hx u hu, hy u hu, sub_zero]

omit [NumberField E] in
theorem at_add {X : Type} [AddCommGroup X] [Module (AF F) X] {x y : X} (hx : At (evFin F v) x) (hy : At (evFin F v) y) :
    At (evFin F v) (x + y) := fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero]

omit [NumberField E] in
theorem at_zero {X : Type} [AddCommGroup X] [Module (AF F) X] : At (evFin F v) (0 : X) := fun u _ => smul_zero u

omit [NumberField E] in
theorem at_mul_left [Fintype κ] {M : Matrix ι κ (AE F E)} (hM : At (evFin F v) M) (N : Matrix κ μ (AE F E)) :
    At (evFin F v) (M * N) := fun u hu => by rw [← Matrix.smul_mul, hM u hu, Matrix.zero_mul]

omit [NumberField E] in
theorem at_mul_right [Fintype κ] (M : Matrix ι κ (AE F E)) {N : Matrix κ μ (AE F E)} (hN : At (evFin F v) N) :
    At (evFin F v) (M * N) := fun u hu => by rw [← Matrix.mul_smul, hN u hu, Matrix.mul_zero]

omit [NumberField E] in
theorem at_mulVec_left [Fintype κ] {M : Matrix ι κ (AE F E)} (hM : At (evFin F v) M) (y : κ → AE F E) :
    At (evFin F v) (M *ᵥ y) := fun u hu => by rw [← Matrix.smul_mulVec, hM u hu, Matrix.zero_mulVec]

omit [NumberField E] in
theorem at_mulVec_right [Fintype κ] (M : Matrix ι κ (AE F E)) {y : κ → AE F E} (hy : At (evFin F v) y) :
    At (evFin F v) (M *ᵥ y) := fun u hu => by rw [← Matrix.mulVec_smul, hy u hu, Matrix.mulVec_zero]

omit [NumberField E] in
theorem at_transpose {M : Matrix ι κ (AE F E)} (hM : At (evFin F v) M) : At (evFin F v) Mᵀ := fun u hu => by
  rw [← Matrix.transpose_smul, hM u hu, Matrix.transpose_zero]

omit [NumberField E] in
theorem at_map {M : Matrix ι κ (AE F E)} (hM : At (evFin F v) M) : At (evFin F v) (M.map (cA σ)) := fun u hu =>
  Matrix.ext fun i j => by
    change u • cA σ (M i j) = 0
    rw [← map_smul, show u • M i j = 0 from congrFun (congrFun (hM u hu) i) j, map_zero]

theorem piE_mulVec [Fintype κ] (h : w.under (𝓞 F) = v) (M : Matrix ι κ (AE F E)) (y : κ → AE F E) :
    piE h ∘ (M *ᵥ y) = M.map (piE h) *ᵥ (piE h ∘ y) := funext fun i => RingHom.map_mulVec (piE h) M y i

theorem map_gram {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
    (J : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) ι (AE F E)) (N : Matrix (Fin n) κ (AE F E)) :
    (Mᵀ * incM F J * N.map (cA σ)).map (piE h) =
      (M.map (piE h))ᵀ * J.map (algebraMap E (w.adicCompletion E)) * (N.map (piE h)).map c := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 1
  · congr 1
    exact Matrix.ext fun i j => piE_incl h _
  · exact Matrix.ext fun i j => piE_cA hc _

end Mat

theorem mem_latW_iff (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (W : Spc F E n) (y : Fin n → AE F E) :
    y ∈ latW W v ↔ At (evFin F v) y ∧ piE h ∘ y ∈ latAt w W.L := by
  have e0 : ∀ (a : AF F) (x : E), a • inclR (F := F) (AF F) x = a ⊗ₜ[F] x := fun a x => by
    change (a * 1) ⊗ₜ[F] x = _
    rw [mul_one]
  have key : ∀ y ∈ latW W v, At (evFin F v) y ∧ compFin F E v ∘ y ∈ latLoc F W.L v := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, ha', x, hx, rfl⟩ := hy
      refine ⟨fun u hu => funext fun i => ?_, ?_⟩
      · change u • a • inclR (F := F) (AF F) (x i) = 0
        rw [smul_smul, show u * a = 0 from ha u hu, zero_smul]
      · convert tmul_mem_latLoc ha' hx using 1
        exact funext fun i => congrArg (compFin F E v) (e0 a (x i))
    | zero =>
      refine ⟨at_zero, ?_⟩
      convert zero_mem (latLoc F W.L v) using 1
      exact funext fun i => map_zero _
    | add y z _ _ hy hz =>
      refine ⟨at_add hy.1 hz.1, ?_⟩
      convert add_mem hy.2 hz.2 using 1
      exact funext fun i => map_add _ _ _
    | neg y _ hy =>
      refine ⟨by simpa using at_sub at_zero hy.1, ?_⟩
      convert neg_mem hy.2 using 1
      exact funext fun i => map_neg _ _
  have key' : ∀ z ∈ latLoc F W.L v, (fun i => sgE E v (z i)) ∈ latW W v := fun z hz => by
    refine latLoc_induction (p := fun z => (fun i => sgE E v (z i)) ∈ latW W v) (fun a ha x hx => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hz
    · exact AddSubgroup.subset_closure ⟨sg v a, at_sg a, by rwa [ev_sg], x, hx, funext fun i => (e0 _ _).symm⟩
    · convert zero_mem (latW W v) using 1
      exact funext fun i => map_zero _
    · convert add_mem hy hz using 1
      exact funext fun i => map_add _ _ _
    · convert neg_mem hy using 1
      exact funext fun i => map_neg _ _
  refine ⟨fun hy => ⟨(key y hy).1, (mem_latLoc_iff hw h _).1 (key y hy).2⟩, fun hy => ?_⟩
  have h1 := key' _ ((mem_latLoc_iff hw h (compFin F E v ∘ y)).2 hy.2)
  convert h1 using 1
  refine vec_inj hw h (at_sub hy.1 (key _ h1).1) (funext fun i => ?_)
  change toCompl h _ = toCompl h (compFin F E v (sgE E v _))
  rw [comp_sgE]
  rfl

end PositivityTheory.ThKH.Iwas
