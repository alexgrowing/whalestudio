import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationIsoBTriplePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

section SlopeTestRemainingChoices

open scoped Classical
open GlobalTheory.VanishLoc (liftT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (h : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (⅟(2 : R)) * h - (w.1 ⬝ᵥ w'.2) * h2

private theorem rho_rho' {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar R ℂ) (w w' : V) (h : Bf w w' = 0)
    (φ : (κ → R) → ℂ) : d.rho ψ w (d.rho ψ w' φ) = d.rho ψ (w + w') φ := by
  simp only [Darboux.rho]
  rw [schr_schr', map_add]
  have := d.form w w'
  rw [h] at this
  exact sub_eq_zero.mp this.symm

private theorem span_herm {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    (hS : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁) (z : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y := by
  haveI := hS.lat
  let S : Submodule E (Fin n → E) :=
    Submodule.span E {H.x} ⊔ LinearMap.range (Matrix.mulVecLin H.ι) ⊔ Submodule.span E {H.y}
  have hle : Submodule.span E (X.L : Set (Fin n → E)) ≤ S := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hA.split z hz
    refine S.add_mem (S.add_mem ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨u, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hz : z ∈ S := hle (by rw [Submodule.IsLattice.span_eq_top (A := E)]; trivial)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨a₁, ha₁, a₂, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 ha₁
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb
  exact ⟨s, t, u, rfl⟩

private theorem span_ad {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    (hS : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁) (z : Fin n → AE F E) :
    ∃ (s t : AE F E) (u : Fin n₁ → AE F E), z = s • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y := by
  choose s t U hU using fun j : Fin n => span_herm hS hA (Pi.single j 1)
  refine ⟨∑ j, z j * inclR (F := F) (AF F) (s j), ∑ j, z j * inclR (F := F) (AF F) (t j),
    ∑ j, z j • incV F (U j), ?_⟩
  have h : ∀ j, (Pi.single j 1 : Fin n → AE F E) = inclR (F := F) (AF F) (s j) • incV F H.x +
      incM F H.ι *ᵥ incV F (U j) + inclR (F := F) (AF F) (t j) • incV F H.y := fun j => by
    funext a
    have := congrArg (inclR (F := F) (AF F)) (congrFun (hU j) a)
    rw [Pi.apply_single (fun _ => inclR (F := F) (E := E) (AF F)) (fun _ => map_zero _), map_one] at this
    rw [this]
    simp [incV, incM, Matrix.mulVec, dotProduct]
  rw [Matrix.mulVec_sum, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  conv_lhs => rw [pi_eq_sum_univ' z]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h j, Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]

omit [NumberField E] in
private theorem formA_inc {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ (incM F J *ᵥ fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  have h : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun a => rfl
  simp [incV, incM, form, Matrix.mulVec, dotProduct, h]

private theorem coef_eq {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    (hB : B.IsGood σ) (hS : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁) (a t : AE F E) (u : Fin n₁ → AE F E) :
    cA σ (incV F H.x ⬝ᵥ (incM F X.J *ᵥ fun i => cA σ ((a • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y) i))) = t := by
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hc : ∀ z : AE F E, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsym : ∀ x y : Fin n → E, form σ X.J y x = σ (form σ X.J x y) := fun x y => by
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hS.herm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hu : incM F H.ι *ᵥ u = ∑ j, u j • incV F (H.ι *ᵥ Pi.single j 1) := by
    funext i
    simp [incV, incM, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  have e : (fun i => cA σ ((a • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y) i)) =
      cA σ a • (fun i => cA σ (incV F H.x i)) + ∑ j, cA σ (u j) • (fun i => cA σ (incV F (H.ι *ᵥ Pi.single j 1) i)) +
        cA σ t • fun i => cA σ (incV F H.y i) := by
    funext i
    simp only [hu, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_add, map_mul, map_sum]
  have h0 : ∀ v, form σ X.J H.x (H.ι *ᵥ v) = 0 := fun v => by rw [hsym, (hA.orth v).1, map_zero]
  rw [e]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul,
    formA_inc, hA.xx, hA.xy, h0, map_zero, map_one, smul_zero, Finset.sum_const_zero, zero_add, smul_eq_mul, mul_one, mul_zero, hc]

omit [NumberField E] in
private theorem unit_move {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) (x u : Fin n → AE F E) :
    (mat k⁻¹ *ᵥ x) ⬝ᵥ (incM F J *ᵥ fun i => cA σ (u i)) = x ⬝ᵥ (incM F J *ᵥ fun i => cA σ ((mat k *ᵥ u) i)) := by
  have hk : (mat k)ᵀ * incM F J * (mat k).map (cA σ) = incM F J := k.2
  have h1 : mat k * mat k⁻¹ = 1 := k.1.mul_inv
  have h2 : (fun i => cA σ ((mat k *ᵥ u) i)) = (mat k).map (cA σ) *ᵥ fun i => cA σ (u i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  conv_lhs => arg 2; rw [← hk]
  rw [h2, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_mulVec]

private theorem partFin_vec {n d : ℕ} (v : Pl F) (a : Fin n → AE F E) (w : Fin d → AE F E) :
    partFin v (Matrix.vecMulVec a w) = Matrix.vecMulVec (GlobalTheory.LatVac.liftV v 1 • a) w := by
  rw [partFin, Matrix.smul_vecMulVec]

private theorem rho_add {B : Base F E} {n d d₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}
    (M : Model σ X W) {H' : Plane E d d₁} (hH' : H'.IsAdapted σ B W W₁ j₀ j₁) (hψ : IsStd B.ψ) (v : Pl F)
    (a b : Fin n → AE F E) {f : (Fin n × Fin d → Fv F v) → ℂ} (hf : f ∈ SB (Fin n × Fin d → Fv F v)) :
    locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec a (incV F H'.x))))
      (locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec b (incV F H'.x)))) f) =
    locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec (a + b) (incV F H'.x)))) f := by
  have a1 := (locOp_rho M.co hψ.1 v (Matrix.vecMulVec b (incV F H'.x)) hf).1
  have a2 := (locOp_rho M.co hψ.1 v (Matrix.vecMulVec a (incV F H'.x))
    (locOp_mem v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec b (incV F H'.x)))) f)).1
  refine (locOp_eq hf (locOp_mem _ _ _) fun r hr => ?_).symm
  have hr' : Rest (evFin F v) (locOp v (M.co.rho B.ψ (partFin v (Matrix.vecMulVec b (incV F H'.x)))) f) r :=
    ⟨hr.1, by rw [← a1 r hr]; exact GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ _ _ hr.2⟩
  rw [← a2 r hr', ← a1 r hr, rho_rho']
  · rw [Matrix.add_vecMulVec, partFin, partFin, partFin, smul_add]
  · rw [partFin_vec, partFin_vec, GlobalTheory.ArchUniq.Coord.vecMulVec_eq_mul, GlobalTheory.ArchUniq.Coord.vecMulVec_eq_mul]
    exact GlobalTheory.ArchUniq.Coord.sympM_eq_zero _ _ (GlobalTheory.ArchUniq.Coord.gram_xx hH') _ _

private theorem compFin_cA' (v : Pl F) (x : AE F E) :
    compFin F E v (cA σ x) = sigR (Fv F v) σ (compFin F E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

private theorem compFin_inclR' (v : Pl F) (x : E) :
    compFin F E v (inclR (F := F) (AF F) x) = inclR (F := F) (Fv F v) x := by
  change evFin F v 1 ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] x
  rw [map_one]

private theorem pairV_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (x : Fin n → AE F E)
    (y : Fin n → Fv F v ⊗[F] E) :
    pairV σ J v (atV v x) y = compFin F E v (x ⬝ᵥ (incM F J *ᵥ fun i => cA σ (liftT v (y i)))) := by
  simp only [pairV, atV, incM, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, compFin_cA', compFin_inclR',
    GlobalTheory.LocPair.compFin_liftT]

private theorem partFin_uS {n n₁ d d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (s : Fv F v ⊗[F] E)
    (z : AE F E) :
    partFin v (uS σ H H' v (s + compFin F E v z)) =
      partFin v (Matrix.vecMulVec ((cA σ (liftT v s) + cA σ z) • incV F H.y) (incV F H'.x)) := by
  have h := partFin_liftT v z
  rw [partFin, partFin] at h
  have h' := congrArg (cA σ) h
  rw [map_smul, map_smul] at h'
  rw [partFin, partFin, uS, Matrix.smul_vecMulVec, map_add, map_add, ← smul_assoc, ← smul_assoc, smul_add, smul_add, h']

end SlopeTestRemainingChoices

theorem UpperTheory.local_theta_partition_triple_alt :
    GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
                 (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
                 ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', GlobalTheory.ThK.LemF.IsLocPart G.M' G₁.M' e' ei' ev' →
                 ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F), ∀ k ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
                   ∀ (y : Fin (b + 2) → Fv F v ⊗[F] E) (s : Fv F v ⊗[F] E),
                   evS B G.M' v (ev' v) H H' (locOp v (om' (k, 1)) (locOp v (G.M'.co.rho B.ψ (partFin v (yAt H' v y))) φ)) s =
                     evS B G.M' v (ev' v) H H' (locOp v (om' (k, 1)) φ) (s + pairV σ G.V'.J v (atV v (mat k⁻¹ *ᵥ incV F H.x)) y) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e he ei ev hL X om om' om₁ om₁' hT hT₁ v k hk φ hφ y s
  have hPr := GlobalTheory.ThK.Inhab.pairV' hT
  have hB := hT.base
  have hone : mat (1 : UA σ G.W.J) = 1 := rfl
  have h1 : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := fun u _ => by
    rw [hone, sub_self, smul_zero]
  have hinv : ∀ u, partFin v u ∈ isoB H H' → ∀ f ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
      ev v (locOp v (G.M'.co.rho B.ψ (partFin v u)) f) = ev v f := fun u hu f hf => by
    rw [← partFin_of_at (at_partFin v u), (locOp_rho G.M'.co hB.std.1 v _ hf).2]
    exact GlobalTheory.T.evaluation_iso_b_triple_pair B G G₁ H H' e he X om om' om₁ om₁' hT hT₁ ei ev hL.1 hL.2.1 hL.2.2 v _ hu (at_partFin v u) f hf
  have hm := GlobalTheory.T.local_weil_action_compatibility hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hPr v k 1 hk h1 (yAt H' v y) φ hφ
  rw [hone, Matrix.transpose_one, Matrix.mul_one] at hm
  have hψ := locOp_mem v (om' (k, 1)) φ
  obtain ⟨c, t, u, hu⟩ := span_ad hT.geo.hV' hC.hH (mat k *ᵥ fun i => GlobalTheory.VanishLoc.liftT v (y i))
  rw [evS, evS, hm, pairV_eq, partFin_uS, unit_move, yAt, Matrix.mul_vecMulVec, hu, coef_eq hB hT.geo.hV' hC.hH, uS,
    ← Matrix.smul_vecMulVec, rho_add G.M' hC.hH' hB.std v _ _ hψ,
    show cA σ (GlobalTheory.VanishLoc.liftT v s) • incV F H.y + (c • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y) =
      c • incV F H.x + (incM F H.ι *ᵥ u + (cA σ (GlobalTheory.VanishLoc.liftT v s) + t) • incV F H.y) by rw [add_smul]; abel,
    ← rho_add G.M' hC.hH' hB.std v _ _ hψ, hinv _ _ _ (locOp_mem _ _ _), ← rho_add G.M' hC.hH' hB.std v _ _ hψ,
    hinv _ _ _ (locOp_mem _ _ _)]
  · exact Or.inr ⟨GlobalTheory.LatVac.liftV v 1 • u, by rw [partFin_vec, Matrix.mulVec_smul]⟩
  · exact Or.inl ⟨GlobalTheory.LatVac.liftV v 1 • c • incV F H'.x, by
      rw [partFin, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, Matrix.vecMulVec_smul]⟩
