import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.CompFinLiftE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ItemsThkhLocrep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LocRepExK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsWeilLatticeDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsSeparatingOfNotMemLatticeCoset

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace UpperTheory.TP.BA
section Schr
variable {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ]
private theorem schr_comp_pk (ψ : AddChar R ℂ) (w w' : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' f) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') f := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h
private theorem schr_comm_pk (ψ : AddChar R ℂ) (w w' : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' f) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w f) := by
  rw [schr_comp_pk, schr_comp_pk, add_comm w' w, smul_smul, ← AddChar.map_add_eq_mul]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) * h
private theorem schr_add_of_pk (ψ : AddChar R ℂ) {w w' : (κ → R) × (κ → R)} (h : w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0)
    (f : (κ → R) → ℂ) : schr ψ (w + w') f = schr ψ w (schr ψ w' f) := by
  rw [schr_comp_pk, h, mul_zero, AddChar.map_zero_eq_one, one_smul]
private theorem schr_zero_pk (ψ : AddChar R ℂ) (f : (κ → R) → ℂ) : schr ψ 0 f = f := by
  funext x
  simp [schr]
private theorem schr_neg_pk (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) :
    schr ψ (-w) (schr ψ w f) = f := by
  rw [← schr_add_of_pk ψ (by simp [dotProduct_comm]), neg_add_cancel, schr_zero_pk]
end Schr
section Alg
private theorem cong_key_pk {A : Type} [Ring A] {e s m m' α β q q' : A} (hs : ∀ a : A, s * a = a * s)
    (h : m * (e - s * β) = e + s * α) (hmm : m' * m = 1) (hq : (e - s * β) * q = e) (hq' : (e + s * α) * q' = e)
    (eq : e * q = q) (eq' : e * q' = q') (eα : α * e = α) (eβ : β * e = β) (e1 : e * α = α) (e2 : e * β = β)
    (e3 : e * e = e) (hm : (m - 1) * e = m - 1) (hm' : (m' - 1) * e = m' - 1) :
    m - 1 = s * (α + β * q + s * (α * (β * q))) ∧ m' - 1 = s * (-β - α * q' + s * (β * (α * q'))) := by
  have a1 : q = e + s * (β * q) := by
    have : e * q - s * β * q = e := by rw [← sub_mul]; exact hq
    rw [eq] at this
    rw [← this, mul_assoc]
    abel
  have a2 : q' = e - s * (α * q') := by
    have : e * q' + s * α * q' = e := by rw [← add_mul]; exact hq'
    rw [eq'] at this
    rw [← this, mul_assoc]
    abel
  have b1 : m * e = (e + s * α) * q := by rw [← h, mul_assoc, hq]
  have b2 : m' * e = (e - s * β) * q' := by
    calc m' * e = m' * ((e + s * α) * q') := by rw [hq']
      _ = m' * (m * (e - s * β) * q') := by rw [h]
      _ = (m' * m) * (e - s * β) * q' := by simp only [mul_assoc]
      _ = _ := by rw [hmm, one_mul]
  have c : ∀ a b : A, a * (s * b) = s * (a * b) := fun a b => by rw [← mul_assoc, ← hs a, mul_assoc]
  have a3 : α * q = α + s * (α * (β * q)) := by
    conv_lhs => rw [a1]
    rw [mul_add, eα, c]
  have a4 : β * q' = β - s * (β * (α * q')) := by
    conv_lhs => rw [a2]
    rw [mul_sub, eβ, c]
  constructor
  · rw [← hm, sub_mul, one_mul, b1]
    calc (e + s * α) * q - e = q + s * (α * q) - e := by rw [add_mul, eq, mul_assoc]
      _ = (e + s * (β * q)) + s * (α + s * (α * (β * q))) - e := by rw [a3, ← a1]
      _ = _ := by rw [mul_add, mul_add, mul_add]; abel
  · rw [← hm', sub_mul, one_mul, b2]
    calc (e - s * β) * q' - e = q' - s * (β * q') - e := by rw [sub_mul, eq', mul_assoc]
      _ = (e - s * (α * q')) - s * (β - s * (β * (α * q'))) - e := by rw [a4, ← a2]
      _ = _ := by simp only [mul_add, mul_sub, mul_neg]; abel
end Alg
section Geo
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
private theorem sg_mul_pk (v : Pl F) (a b : Fv F v) : sg v a * sg v b = sg v (a * b) := by
  rw [PositivityTheory.ThKH.Iwas.mul_sg, PositivityTheory.ThKH.Iwas.ev_sg]
private theorem sg_one_smul_pk {v : Pl F} {A : Type} [AddCommGroup A] [Module (AF F) A] {z : A} (h : At (evFin F v) z) :
    sg v 1 • z = z := PositivityTheory.KCo.at_iff.1 h
private theorem at_sg_smul_pk {v : Pl F} {A : Type} [AddCommGroup A] [Module (AF F) A] (t : Fv F v) (z : A) :
    At (evFin F v) (sg v t • z) := fun u hu => by
  rw [smul_smul, PositivityTheory.ThKH.Iwas.mul_sg, hu, zero_mul, map_zero, zero_smul]
private theorem hTens_zero'_pk {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (c : K →ₐ[R] K) (JA : Matrix (Fin n) (Fin n) K)
    (JB : Matrix (Fin d) (Fin d) K) (p q : Matrix (Fin n) (Fin n) K) (x : Matrix (Fin n) (Fin d) K)
    (h : x * JB * (x.map c)ᵀ = 0) : hTens c JA JB (p * x) (q * x) = 0 := by
  have m : ∀ {a b e : ℕ} (A : Matrix (Fin a) (Fin b) K) (B : Matrix (Fin b) (Fin e) K), (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := c.toRingHom)
  have h' : x.map c * JBᵀ * xᵀ = 0 := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [PositivityTheory.KCo.hTens_eq, m, Matrix.transpose_mul]
  calc (xᵀ * pᵀ * JA * (q.map c * x.map c) * JBᵀ).trace = (xᵀ * (pᵀ * JA * q.map c * (x.map c * JBᵀ))).trace := by
        simp only [Matrix.mul_assoc]
    _ = ((pᵀ * JA * q.map c * (x.map c * JBᵀ)) * xᵀ).trace := Matrix.trace_mul_comm _ _
    _ = 0 := by rw [Matrix.mul_assoc, h', Matrix.mul_zero, Matrix.trace_zero]
private theorem symp_zero'_pk {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (c : K →ₐ[R] K) (ξ : K) (JA : Matrix (Fin n) (Fin n) K)
    (JB : Matrix (Fin d) (Fin d) K) (p q : Matrix (Fin n) (Fin n) K) (x : Matrix (Fin n) (Fin d) K)
    (h : x * JB * (x.map c)ᵀ = 0) : symp (R := R) c ξ JA JB (p * x) (q * x) = 0 := by
  rw [symp, hTens_zero'_pk c JA JB p q x h, mul_zero, map_zero]
variable {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d}
private theorem at_mat_inv_pk {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) : g⁻¹ ∈ UAt σ X (evFin F v) := by
  have e : mat g⁻¹ - 1 = -mat g⁻¹ * (mat g - 1) := by
    rw [mul_sub, neg_mul, show mat g⁻¹ * mat g = 1 from g.1.inv_mul]
    simp [neg_add_eq_sub]
  show At (evFin F v) (mat g⁻¹ - 1)
  rw [e]
  exact PositivityTheory.ThKH.Iwas.at_mul_right _ hg
private theorem mem_UAt_of_locGrp_pk {v : Pl F} {g : UA σ X.J} (hg : g ∈ GlobalTheory.ThK.Dbl.locGrp σ X v) : g ∈ UAt σ X (evFin F v) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact PositivityTheory.ThKH.Locrep.one_mem_UAt X v
  | mul x y _ _ hx hy => exact PositivityTheory.ThKH.Locrep.mul_mem_UAt hx hy
  | inv x _ hx => exact at_mat_inv_pk hx
private def cong_pk (v : Pl F) (Λ : AddSubgroup (Matrix (Fin n) (Fin n) (AE F E))) (s : AF F)
    (h1 : ∀ a ∈ Λ, ∀ b ∈ Λ, a * b ∈ Λ) (h2 : ∀ a ∈ Λ, s • a ∈ Λ) : Subgroup (UA σ X.J) where
  carrier := {g | g ∈ UAt σ X (evFin F v) ∧ (∃ a ∈ Λ, mat g - 1 = s • a) ∧ ∃ a ∈ Λ, mat g⁻¹ - 1 = s • a}
  one_mem' := ⟨PositivityTheory.ThKH.Locrep.one_mem_UAt X v, ⟨0, zero_mem _, by simp [mat]⟩, ⟨0, zero_mem _, by simp [mat]⟩⟩
  mul_mem' := fun {g h} ⟨a1, ⟨a, ha, ea⟩, ⟨a', ha', ea'⟩⟩ ⟨b1, ⟨b, hb, eb⟩, ⟨b', hb', eb'⟩⟩ => by
    have key : ∀ (p q a b : Matrix (Fin n) (Fin n) (AE F E)), p - 1 = s • a → q - 1 = s • b →
        p * q - 1 = s • (a + b + s • (a * b)) := fun p q a b e1 e2 => by
      have p1 : p = 1 + s • a := by rw [← e1]; abel
      have q1 : q = 1 + s • b := by rw [← e2]; abel
      rw [p1, q1]
      simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add]
      abel
    refine ⟨PositivityTheory.ThKH.Locrep.mul_mem_UAt a1 b1, ⟨_, add_mem (add_mem ha hb) (h2 _ (h1 _ ha _ hb)), key _ _ _ _ ea eb⟩,
      ⟨_, add_mem (add_mem hb' ha') (h2 _ (h1 _ hb' _ ha')), ?_⟩⟩
    rw [mul_inv_rev]
    exact key _ _ _ _ eb' ea'
  inv_mem' := fun {g} ⟨a1, p, q⟩ => ⟨at_mat_inv_pk a1, q, by rw [inv_inv]; exact p⟩
end Geo
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
  {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d}
private abbrev Sc_pk (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : (Fin n × Fin d → Fv F v) → ℂ) : (Fin n × Fin d → Fv F v) → ℂ :=
  schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v u) f
private abbrev Bf_pk (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (u y : Matrix (Fin n) (Fin d) (AE F E)) : AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u y
private theorem sc_comm_pk (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : At (evFin F v) u) (y) (f) : Sc_pk M ψ v u (Sc_pk M ψ v y f) = ψ (Bf_pk σ X W u y) • Sc_pk M ψ v y (Sc_pk M ψ v u f) := by
  rw [Sc_pk, Sc_pk, schr_comm_pk]
  congr 1
  exact (GlobalTheory.LatVac.DualLoc.psi_form M.co v ψ hu y).symm
private theorem sc_add_pk (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) {u y : Matrix (Fin n) (Fin d) (AE F E)}
    (h : Bf_pk σ X W u y = 0) (f) : Sc_pk M ψ v (u + y) f = Sc_pk M ψ v u (Sc_pk M ψ v y f) := by
  have := GlobalTheory.LatVac.DualLoc.evFin_form M.co v u y
  rw [show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u y = 0 from h, map_zero] at this
  rw [Sc_pk, map_add]
  exact schr_add_of_pk _ this.symm f
private theorem sc_neg_pk (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) (u) (f) : Sc_pk M ψ v (-u) (Sc_pk M ψ v u f) = f := by
  rw [Sc_pk, Sc_pk, map_neg]
  exact schr_neg_pk _ _ f
private theorem schr_smul_pk {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w : (κ → R) × (κ → R)) (c : ℂ) (f : (κ → R) → ℂ) : schr ψ w (c • f) = c • schr ψ w f := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  ring
private theorem bf_sub_pk (M : Model σ X W) (u y y' : Matrix (Fin n) (Fin d) (AE F E)) :
    Bf_pk σ X W u (y - y') = Bf_pk σ X W u y - Bf_pk σ X W u y' := by
  simp only [Bf_pk, M.co.form, map_sub, Prod.fst_sub, Prod.snd_sub, dotProduct_sub, sub_dotProduct]
  ring
private theorem symp_g_pk (ξ : AE F E) (g : UA σ X.J) (u y : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) (mat g * u) (mat g * y) =
      symp (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) u y := by
  have := PositivityTheory.KCo.symp_act (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) (g, (1 : UA σ W.J)) u y
  simpa [actAB, mat] using this
end Main
section Thm
open UpperTheory.TP
theorem _root_.UpperTheory.TP.bumpAny_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.BumpAny_k := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP hn hd v N hN
  classical
  obtain ⟨ω, ρ, L⟩ := _root_.PositivityTheory.ThKH.Locrep.locRepEx_k F E σ n d B X W M om
    ⟨hP.base, ⟨n, 0, hP.herm⟩, ⟨d, 0, hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  obtain ⟨Λ, x₁, r, ϖ, D⟩ := _root_.UpperTheory.exists_weilLatticeDatum F E σ B n d X W n 0 d 0 hP.base hP.herm hP.skew hd v
  obtain ⟨hvS, hv0, θ, hθ, hvac⟩ := hP.good.vac v
  have hat : ∀ γ ∈ latAtV X W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have hone : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := PositivityTheory.ThKH.Locrep.one_mem_UAt W v
  obtain ⟨U, hU, hUf⟩ := (T.acts F E σ B n d X W M χX χW om n 0 d 0 hP v).2.2 (M.vac v) hvS
  have hU1 : {g : UA σ X.J | (g, (1 : UA σ W.J)) ∈ U} ∈ 𝓝 (1 : UA σ X.J) := by
    have c : Continuous fun g : UA σ X.J => (g, (1 : UA σ W.J)) := continuous_id.prodMk continuous_const
    exact c.continuousAt.preimage_mem_nhds (show U ∈ 𝓝 ((1 : UA σ X.J), (1 : UA σ W.J)) from hU)
  have hI : {g : UA σ X.J | GlobalTheory.ThK.Dbl.IntAt v g} ∈ 𝓝 (1 : UA σ X.J) :=
    (GlobalTheory.ThK.Dbl.Euler.isOpen_int (σ := σ) hP.herm.lat v).mem_nhds (one_mem _)
  obtain ⟨k₀, hk₀⟩ := D.small _ (Filter.inter_mem hN (Filter.inter_mem hU1 hI))
  obtain ⟨k, hk⟩ : ∃ k, k = k₀ + 1 := ⟨_, rfl⟩
  have hϖO : ∀ m : ℕ, ϖ ^ m ∈ v.adicCompletionIntegers F := fun m => pow_mem D.ϖ_mem m
  obtain ⟨s, hs⟩ : ∃ s, s = sg v (ϖ ^ k) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = sg v (ϖ ^ k)⁻¹ := ⟨_, rfl⟩
  have ss : s * s' = sg v 1 := by rw [hs, hs', sg_mul_pk, mul_inv_cancel₀ (pow_ne_zero _ D.ϖ_ne)]
  have hsΛ : ∀ a ∈ Λ, s • a ∈ Λ := fun a ha => hs ▸ D.smul_mem _ (hϖO k) a ha
  let H : Subgroup (UA σ X.J) := cong_pk v Λ s D.mul_mem hsΛ
  have memH : ∀ g, g ∈ H ↔ g ∈ UAt σ X (evFin F v) ∧ (∃ a ∈ Λ, mat g - 1 = s • a) ∧ ∃ a ∈ Λ, mat g⁻¹ - 1 = s • a :=
    fun g => Iff.rfl
  have hsm : ∀ g ∈ H, g ∈ N ∩ ({g : UA σ X.J | (g, (1 : UA σ W.J)) ∈ U} ∩ {g : UA σ X.J | GlobalTheory.ThK.Dbl.IntAt v g}) := fun g hg => by
    obtain ⟨h1, h2, h3⟩ := (memH g).1 hg
    exact hk₀ k (by omega) g h1 (hs ▸ h2) (hs ▸ h3)
  have hx₁ := hat _ D.x_mem
  obtain ⟨x0, hx0d⟩ : ∃ x0, x0 = s' • x₁ := ⟨_, rfl⟩
  have hx0 : At (evFin F v) x0 := hx0d ▸ hs' ▸ at_sg_smul_pk _ _
  have hsx0 : s • x0 = x₁ := by rw [hx0d, smul_smul, ss, sg_one_smul_pk hx₁]
  obtain ⟨φ, hφd⟩ : ∃ φ, φ = Sc_pk M B.ψ v x0 (M.vac v) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin d) (AE F E) → ℂ, Q = fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) := ⟨_, rfl⟩
  have hSρ : ∀ u, At (evFin F v) u → ∀ f ∈ SB (Fin n × Fin d → Fv F v), Sc_pk M B.ψ v u f = ρ u f := fun u hu f hf =>
    (L.actsH u hu f hf _).1 (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu f)
  have hφS : φ ∈ SB (Fin n × Fin d → Fv F v) := by
    rw [hφd, hSρ _ hx0 _ hvS]
    exact L.presH _ hx0 _ hvS
  have hφ0 : φ ≠ 0 := fun h0 => hv0 (by
    have := sc_neg_pk M B.ψ v x0 (M.vac v)
    rw [← hφd, h0] at this
    rw [← this]
    funext x
    simp [schr])
  have hSv : ∀ γ ∈ latAtV X W v, Sc_pk M B.ψ v γ (M.vac v) = Q γ • M.vac v := fun γ hγ =>
    GlobalTheory.TensUniq.eq_of_tens_eq v (M.vac v) _ _ hvS fun r' hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hat γ hγ) (M.vac v) r' hr).symm.trans (by rw [hQ]; exact hvac γ hγ r' hr)
  have E1 : ∀ γ ∈ latAtV X W v, Sc_pk M B.ψ v γ φ = (B.ψ (Bf_pk σ X W γ x0) * Q γ) • φ := fun γ hγ => by
    rw [hφd, sc_comm_pk M B.ψ v (hat γ hγ), hSv γ hγ, Sc_pk, schr_smul_pk, smul_smul]
  have hA : ∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) φ ((B.ψ (Bf_pk σ X W γ x0) * Q γ) • φ) := fun γ hγ => by
    rw [← E1 γ hγ]
    exact GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hat γ hγ) φ
  have hfix : ∀ g ∈ H, Acts (evFin F v) (om (g, 1)) φ φ := fun g hg => by
    obtain ⟨h1, ⟨a, ha, ea⟩, -⟩ := (memH g).1 hg
    have vf : Acts (evFin F v) (om (g, 1)) (M.vac v) (M.vac v) := hUf (g, 1) (hsm g hg).2.1 h1 hone
    have w1 : M.vac v = ω (g, 1) (M.vac v) := (L.acts g h1 1 hone _ hvS _).1 vf
    refine (L.acts g h1 1 hone φ hφS φ).2 ?_
    have hγ := D.act a ha x₁ D.x_mem
    have e1 : mat g * x0 * (mat (1 : UA σ W.J))ᵀ = x0 + a * x₁ := by
      rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.transpose_one, Matrix.mul_one,
        show mat g = 1 + (mat g - 1) by abel, Matrix.add_mul, Matrix.one_mul, ea]
      congr 1
      rw [hx0d, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ss, sg_one_smul_pk (hat _ hγ)]
    have hb0 : Bf_pk σ X W x0 (a * x₁) = 0 := by
      have := symp_zero'_pk (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (s' • 1) a x₁ D.gram
      rwa [Matrix.smul_mul, Matrix.one_mul, ← hx0d] at this
    have hq1 : Q (a * x₁) = 1 := by
      rw [hQ]
      show B.ψ _ = 1
      rw [symp_zero'_pk (R := AF F) (cA σ) _ (incM F X.J) (incM F W.J) a a x₁ D.gram, mul_zero, AddChar.map_zero_eq_one]
    have e2 := L.impl g h1 1 hone x0 hx0 (M.vac v) hvS
    rw [e1, ← w1, ← hSρ _ hx0 _ hvS, ← hφd, ← hSρ _ (PositivityTheory.ThKH.Iwas.at_add hx0 (hat _ hγ)) _ hvS, sc_add_pk M B.ψ v hb0,
      hSv _ hγ, hq1, one_smul, ← hφd] at e2
    exact e2.symm
  have hsep : ∀ g ∈ GlobalTheory.ThK.Dbl.locGrp σ X v, g ∉ H → ∃ (u : Matrix (Fin n) (Fin d) (AE F E)) (c c' : ℂ), At (evFin F v) u ∧ c ≠ c' ∧
      Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) ∧ Acts (evFin F v) (M.co.rho B.ψ (mat g * u)) φ (c' • φ) := fun g hgl hgH => by
    have hg := mem_UAt_of_locGrp_pk hgl
    have hg' := at_mat_inv_pk hg
    have hgm : mat g * mat g⁻¹ = 1 := g.1.mul_inv
    obtain ⟨y, hyd⟩ : ∃ y, y = mat g⁻¹ * x0 - x0 := ⟨_, rfl⟩
    have hy : At (evFin F v) y := hyd ▸ PositivityTheory.ThKH.Iwas.at_sub (PositivityTheory.ThKH.Iwas.at_mul_right _ hx0) hx0
    by_cases hc : ∀ a ∈ latAtV X W v, ∀ b ∈ latAtV X W v, y ≠ a + mat g⁻¹ * b
    · obtain ⟨u, hu, hgu, hne⟩ := _root_.UpperTheory.exists_separating_of_not_mem_lattice_coset F E σ B n d X W M n 0 d 0 hP.base hP.herm hP.skew v g hg y hy hc
      have hq : Q (mat g * u) = Q u := by
        rw [hQ]
        show B.ψ _ = B.ψ _
        rw [symp_g_pk]
      have hb : Bf_pk σ X W (mat g * u) x0 = Bf_pk σ X W u (mat g⁻¹ * x0) := by
        have := symp_g_pk (W := W) (-1) g u (mat g⁻¹ * x0)
        rwa [← Matrix.mul_assoc, hgm, Matrix.one_mul] at this
      have hQ0 : Q u ≠ 0 := by
        rw [hQ]
        exact (B.ψ.val_isUnit _).ne_zero
      refine ⟨u, _, _, hat u hu, ?_, hA u hu, hA _ hgu⟩
      intro h
      apply hne
      have h3 : B.ψ (Bf_pk σ X W u x0) = B.ψ (Bf_pk σ X W (mat g * u) x0) := mul_right_cancel₀ hQ0 (by rw [h, hq])
      rw [hyd]
      show B.ψ (Bf_pk σ X W u _) = 1
      rw [bf_sub_pk M, AddChar.map_sub_eq_div, ← hb, ← h3, div_self (B.ψ.val_isUnit _).ne_zero]
    · exfalso
      apply hgH
      push Not at hc
      obtain ⟨a, ha, b, hb, e⟩ := hc
      have hα := D.r_mem a ha
      have hβ := D.r_mem b hb
      obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin n) (Fin n) (AE F E), S = s • 1 := ⟨_, rfl⟩
      have hSx : ∀ {l : ℕ} (x : Matrix (Fin n) (Fin l) (AE F E)), S * x = s • x := fun x => by
        rw [hS, Matrix.smul_mul, Matrix.one_mul]
      have hcomm : ∀ x : Matrix (Fin n) (Fin n) (AE F E), S * x = x * S := fun x => by
        rw [hSx, hS, Matrix.mul_smul, Matrix.mul_one]
      have e0 : mat g⁻¹ * (x₁ - s • b) = x₁ + s • a := by
        have e' : mat g⁻¹ * x0 = x0 + a + mat g⁻¹ * b := by
          rw [add_assoc, ← e, hyd]
          abel
        calc mat g⁻¹ * (x₁ - s • b) = s • (mat g⁻¹ * x0 - mat g⁻¹ * b) := by
              rw [← hsx0, ← smul_sub, Matrix.mul_smul, Matrix.mul_sub]
          _ = s • (x0 + a) := by
              rw [e']
              congr 1
              abel
          _ = x₁ + s • a := by rw [smul_add, hsx0]
      have hkey : mat g⁻¹ * (eM v n - S * (b * r)) = eM v n + S * (a * r) := by
        rw [← D.right, hSx, hSx, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.sub_mul, ← Matrix.add_mul, ← Matrix.mul_assoc, e0]
      have hsk : ∀ p : Matrix (Fin n) (Fin n) (AE F E), sg v ϖ • (sg v (ϖ ^ k₀) • p) = s • p := fun p => by
        rw [smul_smul, sg_mul_pk, hs, hk, pow_succ']
      obtain ⟨q, hq, hq1⟩ := D.unit (sg v (ϖ ^ k₀) • (-(b * r))) (D.smul_mem _ (hϖO _) _ (neg_mem hβ))
      obtain ⟨q', hq', hq1'⟩ := D.unit (sg v (ϖ ^ k₀) • (a * r)) (D.smul_mem _ (hϖO _) _ hα)
      rw [hsk, smul_neg, ← sub_eq_add_neg, ← hSx] at hq1
      rw [hsk, ← hSx] at hq1'
      have eL : ∀ x ∈ Λ, eM v n * x = x := fun x hx => by
        rw [Matrix.smul_mul, Matrix.one_mul, sg_one_smul_pk (D.at_mem x hx)]
      have eR : ∀ x : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) x → x * eM v n = x := fun x hx => by
        rw [Matrix.mul_smul, Matrix.mul_one, sg_one_smul_pk hx]
      obtain ⟨c1, c2⟩ := cong_key_pk (s := S) (m := mat g⁻¹) (m' := mat g) hcomm hkey hgm hq1 hq1' (eL q hq) (eL q' hq')
        (eR _ (D.at_mem _ hα)) (eR _ (D.at_mem _ hβ)) (eL _ hα) (eL _ hβ) (eL _ D.one_mem) (eR _ hg') (eR _ hg)
      simp only [hSx] at c1 c2
      exact (memH g).2 ⟨hg, ⟨_, add_mem (sub_mem (neg_mem hβ) (D.mul_mem _ hα _ hq')) (hsΛ _ (D.mul_mem _ hβ _ (D.mul_mem _ hα _ hq'))), c2⟩,
        ⟨_, add_mem (add_mem hα (D.mul_mem _ hβ _ hq)) (hsΛ _ (D.mul_mem _ hα _ (D.mul_mem _ hβ _ hq))), c1⟩⟩
  refine ⟨H, φ, ⟨hφS, hφ0, fun g hg => Subgroup.subset_closure ((memH g).1 hg).1, fun g hg => (hsm g hg).2.2, ?_, hfix, hsep⟩,
    fun g hg => (hsm g hg).1⟩
  obtain ⟨O, hO, h1, hOg⟩ := D.nbhd k
  refine ⟨O, hO, h1, fun g hg hgO => ?_⟩
  have hu := mem_UAt_of_locGrp_pk hg
  have := hOg g hu hgO
  exact (memH g).2 ⟨hu, hs ▸ this.1, hs ▸ this.2⟩
end Thm
end UpperTheory.TP.BA
end
end
