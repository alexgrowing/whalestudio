import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InclRMulPtAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)

theorem map_mul_nu {R S : Type} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S)
    {l m k : ℕ} (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin k) R) :
    (A * B).map f = A.map f * B.map f := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

def blow {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (AE F E) :=
  1 + (A - 1).map (ptAt hw h)

theorem blow_one {n : ℕ} : blow hw h (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = 1 := by
  simp [blow, Matrix.map_zero _ (map_zero (ptAt hw h))]

theorem blow_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    blow hw h (A * B) = blow hw h A * blow hw h B := by
  have e : A * B - 1 = (A - 1) + (B - 1) + (A - 1) * (B - 1) := by noncomm_ring
  simp only [blow, e, Matrix.map_add _ (map_add (ptAt hw h)), map_mul_nu]
  noncomm_ring

def blowHom (n : ℕ) : Matrix (Fin n) (Fin n) (w.adicCompletion E) →* Matrix (Fin n) (Fin n) (AE F E) where
  toFun := blow hw h
  map_one' := blow_one hw h
  map_mul' := blow_mul hw h

theorem blow_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) :
    (blow hw h A)ᵀ = blow hw h Aᵀ := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [blow]
  · simp [blow, Matrix.one_apply, hij, Ne.symm hij]

theorem blow_map_cA (σ : E →ₐ[F] E) {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) : (blow hw h A).map (cA σ) = blow hw h (A.map c) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [blow, cA_ptAt hw h σ hc]
  · simp [blow, Matrix.one_apply, hij, cA_ptAt hw h σ hc]

theorem map_pt_mul_incM {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (J : Matrix (Fin n) (Fin n) E) :
    A.map (ptAt hw h) * incM F J = (A * J.map (algebraMap E _)).map (ptAt hw h) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, incM, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, inclR_mul_ptAt, mul_comm]

theorem incM_mul_map_pt {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (J : Matrix (Fin n) (Fin n) E) :
    incM F J * A.map (ptAt hw h) = (J.map (algebraMap E _) * A).map (ptAt hw h) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, incM, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inclR_mul_ptAt]

theorem blow_form {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (A B : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hAB : Aᵀ * J.map (algebraMap E _) * B = J.map (algebraMap E _)) :
    (blow hw h A)ᵀ * incM F J * blow hw h B = incM F J := by
  rw [blow_transpose]
  set Ja := J.map (algebraMap E (w.adicCompletion E))
  have e : (Aᵀ - 1) * Ja + Ja * (B - 1) + (Aᵀ - 1) * Ja * (B - 1) = 0 := by
    have : (Aᵀ - 1) * Ja + Ja * (B - 1) + (Aᵀ - 1) * Ja * (B - 1) = Aᵀ * Ja * B - Ja := by noncomm_ring
    rw [this, hAB, sub_self]
  have e2 : (blow hw h Aᵀ) * incM F J * blow hw h B = incM F J +
      (((Aᵀ - 1) * Ja + Ja * (B - 1) + (Aᵀ - 1) * Ja * (B - 1)).map (ptAt hw h)) := by
    rw [Matrix.map_add _ (map_add (ptAt hw h)), Matrix.map_add _ (map_add (ptAt hw h)), map_mul_nu _ ((Aᵀ - 1) * Ja),
      ← map_pt_mul_incM, ← incM_mul_map_pt]
    simp only [blow]
    noncomm_ring
  rw [e2, e, Matrix.map_zero _ (map_zero (ptAt hw h)), add_zero]

theorem blow_mulVec_pt {n : ℕ} (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (ζ : Fin n → w.adicCompletion E) :
    blow hw h A *ᵥ (fun i => ptAt hw h (ζ i)) = fun i => ptAt hw h ((A *ᵥ ζ) i) := by
  have e1 : (A - 1).map (ptAt hw h) *ᵥ (fun i => ptAt hw h (ζ i)) = fun i => ptAt hw h (((A - 1) *ᵥ ζ) i) := by
    ext i; simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  rw [blow, Matrix.add_mulVec, Matrix.one_mulVec, e1]
  ext i
  rw [Pi.add_apply, ← map_add, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, add_sub_cancel]

theorem pt_mem_latAt {n : ℕ} (X : Spc F E n) {x : Fin n → w.adicCompletion E} (hx : x ∈ GlobalTheory.LFun.latAt w X.L) :
    (fun i => ptAt hw h (x i)) ∈ GlobalTheory.InertSph.latAt X v := by
  suffices H : ∀ c : Formalism.UG.Ov E w, (fun i => ptAt hw h ((c • x) i)) ∈ GlobalTheory.InertSph.latAt X v by
    simpa using H 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    intro c
    obtain ⟨t, ht⟩ := (InertChart.complEquiv hw h).surjective (c : w.adicCompletion E)
    have htI : t ∈ intLoc F E v := (InertChart.mem_intLoc_iff hw h t).2 (by
      rw [show toCompl h t = c from ht]; exact c.2)
    have key : ∀ t ∈ intLoc F E v,
        (fun i => ptAt hw h (toCompl h t * algebraMap E (w.adicCompletion E) (y i))) ∈ GlobalTheory.InertSph.latAt X v := by
      intro s hs
      have hs' : s ∈ AddSubgroup.closure
          {z | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, z = a ⊗ₜ[F] (x : E)} := hs
      clear hs
      induction hs' using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, ha, e, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a,
          by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, e • y, X.L.smul_mem e hy, ?_⟩
        funext i
        rw [Pi.smul_apply, ptAt_apply]
        have e2 : toCompl h (a ⊗ₜ[F] (e : E)) * algebraMap E (w.adicCompletion E) (y i) =
            toCompl h (a ⊗ₜ[F] ((e : E) * y i)) := by
          rw [toCompl_tmul, toCompl_tmul, map_mul, mul_assoc]
        rw [e2, show toCompl h (a ⊗ₜ[F] ((e : E) * y i)) = InertChart.complEquiv hw h (a ⊗ₜ[F] ((e : E) * y i)) from rfl,
          RingEquiv.symm_apply_apply]
        show _ = GlobalTheory.LatVac.liftV v a • ((1 : AF F) ⊗ₜ[F] _)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rfl
      | zero => simp only [map_zero, zero_mul]; exact zero_mem _
      | add a b _ _ ha hb =>
        have e3 : (fun i => ptAt hw h (toCompl h (a + b) * algebraMap E (w.adicCompletion E) (y i))) =
            (fun i => ptAt hw h (toCompl h a * algebraMap E (w.adicCompletion E) (y i))) +
              (fun i => ptAt hw h (toCompl h b * algebraMap E (w.adicCompletion E) (y i))) := by
          funext i; simp [add_mul]
        rw [e3]; exact add_mem ha hb
      | neg a _ ha =>
        have e3 : (fun i => ptAt hw h (toCompl h (-a) * algebraMap E (w.adicCompletion E) (y i))) =
            -(fun i => ptAt hw h (toCompl h a * algebraMap E (w.adicCompletion E) (y i))) := by
          funext i; simp [neg_mul]
        rw [e3]; exact neg_mem ha
    convert key t htI using 2 with i
    show ptAt hw h ((c : w.adicCompletion E) * _) = _
    rw [← ht]; rfl
  | zero => intro c; simp only [smul_zero, Pi.zero_apply, map_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    intro c
    convert add_mem (hx c) (hy c) using 1
    funext i; simp [smul_add]
  | smul a x _ hx =>
    intro c
    convert hx (c * a) using 1
    funext i; rw [mul_smul]

theorem blow_mulVec_mem {n : ℕ} (X : Spc F E n) (A : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hA : ∀ x ∈ GlobalTheory.LFun.latAt w X.L, A *ᵥ x ∈ GlobalTheory.LFun.latAt w X.L) :
    ∀ z ∈ GlobalTheory.InertSph.latAt X v, blow hw h A *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
    have hat : ∀ i, At (evFin F v) ((a • fun i => inclR (F := F) (AF F) (y i)) i) := fun i u hu => by
      rw [Pi.smul_apply, smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
    have hz : (a • fun i => inclR (F := F) (AF F) (y i)) =
        fun i => ptAt hw h (locW h ((a • fun i => inclR (F := F) (AF F) (y i)) i)) :=
      funext fun i => (ptAt_locW hw h (hat i)).symm
    have hloc : (fun i => locW h ((a • fun i => inclR (F := F) (AF F) (y i)) i)) ∈ GlobalTheory.LFun.latAt w X.L := by
      have e : (fun i => locW h ((a • fun i => inclR (F := F) (AF F) (y i)) i)) =
          (⟨complMap h (evFin F v a), complMap_mem h hav⟩ : Formalism.UG.Ov E w) •
            fun i => algebraMap E (w.adicCompletion E) (y i) := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply]
        show toCompl h (compFin F E v (a • ((1 : AF F) ⊗ₜ[F] y i))) = complMap h (evFin F v a) * _
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rfl
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
    rw [hz, blow_mulVec_pt]
    exact pt_mem_latAt hw h X (hA _ hloc)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem conj_preserves {n : ℕ} (X : Spc F E n) (P : GL (Fin n) (w.adicCompletion E)) (hP : IsFrameAt w X.L P)
    (k : GL (Fin n) (w.adicCompletion E)) (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (w.adicCompletion E))) :
    ∀ x ∈ GlobalTheory.LFun.latAt w X.L,
      ((P * k * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ x ∈
        GlobalTheory.LFun.latAt w X.L := by
  intro x hx
  obtain ⟨k', rfl⟩ := hk
  have hy := (hP (((P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) _) *ᵥ x)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]; exact hx)
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  refine (hP _).1 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hy j)
  exact (k'.1 i j).2

theorem conj_form {K : Type} [CommRing K] {n : ℕ} (c : K →+* K) (Ja p q m : Matrix (Fin n) (Fin n) K) (δ : K)
    (hpq : p * q = 1) (hP : pᵀ * Ja * p.map c = δ • 1) (hk : mᵀ * m.map c = 1) :
    (p * m * q)ᵀ * Ja * (p * m * q).map c = Ja := by
  have hpqc : p.map c * q.map c = 1 := by rw [← Matrix.map_mul, hpq, Matrix.map_one _ (map_zero c) (map_one c)]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.map_mul]
  calc qᵀ * (mᵀ * pᵀ) * Ja * (p.map c * m.map c * q.map c)
      = qᵀ * mᵀ * (pᵀ * Ja * p.map c) * m.map c * q.map c := by simp only [Matrix.mul_assoc]
    _ = δ • (qᵀ * (mᵀ * m.map c) * q.map c) := by
        rw [hP]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = δ • (qᵀ * q.map c) := by rw [hk, Matrix.mul_one]
    _ = qᵀ * (pᵀ * Ja * p.map c) * q.map c := by rw [hP]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    _ = (p * q)ᵀ * Ja * (p.map c * q.map c) := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = Ja := by rw [hpq, hpqc]; simp

variable {Γ : Type} [Group Γ]

def embHom {n : ℕ} (P : GL (Fin n) (w.adicCompletion E)) (φ : Γ →* GL (Fin n) (w.adicCompletion E)) :
    Γ →* GL (Fin n) (AE F E) :=
  (Units.map (blowHom hw h n)).comp ((MulAut.conj P).toMonoidHom.comp φ)

theorem embHom_val {n : ℕ} (P : GL (Fin n) (w.adicCompletion E)) (φ : Γ →* GL (Fin n) (w.adicCompletion E)) (g : Γ) :
    ((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) =
      blow hw h ((P * φ g * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl

end GlobalTheory.InertPlace

open GlobalTheory.InertPlace in
theorem GlobalTheory.InertPlace.exists_hom_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    (σL : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h σL →
    ∀ {n : ℕ} (X : Spc F E n) (P : GL (Fin n) (w.adicCompletion E)) (δ : w.adicCompletion E),
      (P : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) *
        (P : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = δ • 1 →
      ∀ {Γ : Type} [Group Γ] (φ : Γ →* GL (Fin n) (w.adicCompletion E)),
        (∀ g, (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ * (φ g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map σL = 1) →
        ∃ ι : Γ →* UA σ X.J, (∀ g, ι g ∈ UAt σ X (evFin F v)) ∧
          (∀ g, (mat (ι g)).map (locW h) = ((P * φ g * P⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
          (IsFrameAt w X.L P → ∀ g, φ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (w.adicCompletion E)) → ι g ∈ GlobalTheory.InertSph.KAt σ X v) := by
  intro F E _ _ _ _ _ σ v w hw h σL hc n X P δ hPJ Γ _ φ hφ
  have hmem : ∀ g, embHom hw h P φ g ∈ UG (cA σ) (incM F X.J) := fun g => by
    show ((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))ᵀ * incM F X.J *
      ((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)).map (cA σ) = incM F X.J
    rw [embHom_val, blow_map_cA hw h σ hc]
    refine blow_form hw h X.J _ _ ?_
    rw [Units.val_mul, Units.val_mul]
    exact conj_form σL _ _ _ _ δ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hPJ (hφ g)
  have hAt : ∀ g, (embHom hw h P φ).codRestrict (UG (cA σ) (incM F X.J)) hmem g ∈ UAt σ X (evFin F v) := fun g => by
    show At (evFin F v) (((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) - 1)
    rw [embHom_val, blow, add_sub_cancel_left]
    intro u hu
    ext i j
    rw [Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
    exact at_ptAt hw h _ u hu
  refine ⟨(embHom hw h P φ).codRestrict (UG (cA σ) (incM F X.J)) hmem, hAt, fun g => ?_, fun hF g hg => ?_⟩
  · show (((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))).map (locW h) = _
    rw [embHom_val]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [blow, locW_ptAt]
    · simp [blow, Matrix.one_apply, hij, locW_ptAt]
  · refine ⟨hAt g, fun z hz => ⟨?_, ?_⟩⟩
    · show ((embHom hw h P φ g : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ _
      rw [embHom_val]
      exact blow_mulVec_mem hw h X _ (conj_preserves X P hF (φ g) hg) z hz
    · rw [← map_inv]
      show ((embHom hw h P φ g⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ z ∈ _
      rw [embHom_val]
      exact blow_mulVec_mem hw h X _ (conj_preserves X P hF (φ g⁻¹) (by rw [map_inv]; exact inv_mem hg)) z hz
