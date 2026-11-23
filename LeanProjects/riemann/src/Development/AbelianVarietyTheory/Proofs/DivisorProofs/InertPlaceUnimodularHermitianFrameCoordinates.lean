import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameAdelicLatticeAtFinitePlaceOfInertStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularGramInverseInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnramifiedSkewSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedMatrixIffFrameCoordinatesOfInertStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorLatticeAtPlaceIffFrameCoordinatesIntegrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilSymplecticFormFrameCoordinatesEqLocalTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHomConjInverseTransposeAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHomFrameConjugationAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoordinatesActionOfIdentityOffPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAdelicUnitaryPointOfLocalMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeStabilizerOfFrameConjIntegralStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

theorem GlobalTheory.InertLocFrame.frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σL : L →+* L) (q : ℕ)
      (δ : L) (ψL : AddChar L ℂ) (ι : L →+ AE F E),
      Formalism.UG.IsUnramInv ϖ σL q → Odd q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι →
      (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      (∀ x, B.ψ (Algebra.trace (AF F) (AE F E) (ι x)) = ψL (x + σL x)) →
      ∃ (JS : GL (Fin a) L) (JT : GL (Fin (a + a')) L)
        (Xm : Matrix (Fin (a + a')) (Fin a) L →+ Matrix (Fin a) (Fin (a + a')) (AE F E))
        (iV : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L) →* UA σ G.V.J)
        (iW : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
        JS ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
        (∀ i j, σL ((JS : Matrix (Fin a) (Fin a) L) i j) = (JS : Matrix (Fin a) (Fin a) L) j i) ∧
        (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
        (∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (Xm x) (Xm y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) ∧
        (∀ z : Matrix (Fin a) (Fin (a + a')) (AE F E), At (evFin F v) z ↔ ∃ x, Xm x = z) ∧
        (∀ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → Xm u ∈ latAtV G.V G.W v) ∧
        (∀ z ∈ latAtV G.V G.W v, ∃ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧ Xm u = z) ∧
        (∀ g h x, actAB (cA σ) (iV g, iW h) (Xm x) =
          Xm (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
            (((g : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) ∧
        (∀ g, iV g ∈ UAt σ G.V (evFin F v)) ∧ (∀ h, iW h ∈ UAt σ G.W (evFin F v)) ∧
        (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L), (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
          iV g ∈ GlobalTheory.InertSph.KAt σ G.V v) ∧
        (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
          (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → iW h ∈ GlobalTheory.InertSph.KAt σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G hB hG v w hin L _ _ _ ϖ σL q δ ψL ι hunr hodd hδ hinj him hmul hσ hint hψ
  have hδne : δ ≠ 0 := fun h0 => by rw [h0, map_zero] at hδ; exact zero_ne_one hδ.1
  have ent : ∀ {m : ℕ} (g : GL (Fin m) L), g ∈ Formalism.UG.GLint (Fin m) (Formalism.UG.intL L) →
      ∀ i j, (g : Matrix (Fin m) (Fin m) L) i j ∈ Formalism.UG.intL L := by
    rintro m g ⟨g0, rfl⟩ i j
    exact ((g0 : Matrix (Fin m) (Fin m) (Formalism.UG.intL L)) i j).2
  obtain ⟨PV, hPV⟩ := GlobalTheory.T.exists_frame_adelicLatticeAtFinitePlace_of_inert F E v w hin a G.V hG.hV.lat L ι hinj him hmul hint
  obtain ⟨PW, hPW⟩ := GlobalTheory.T.exists_frame_adelicLatticeAtFinitePlace_of_inert F E v w hin (a + a') G.W hG.hW.lat L ι hinj him hmul hint
  obtain ⟨JS, hJS, hJSg, hJSh⟩ := GlobalTheory.T.exists_unimodular_gram_inverse_inertPlace F E σ B hB v w hin a _ _ G.V hG.hV L ϖ σL q ι hunr hinj him hmul hσ hint
    PV hPV
  obtain ⟨JT, hJT, hJTg, hJTh⟩ := GlobalTheory.T.inert_place_unramified_skew_space F E σ B hB v w hin (a + a') _ _ G.W hG.hW L ϖ σL q δ ι hunr hodd hδ hinj
    him hmul hσ hint PW hPW
  obtain ⟨iV, hiV⟩ := GlobalTheory.T.exists_unitary_hom_conjInverseTranspose_at_place F E σ v a G.V L σL ι him hmul hσ PV JS hJSg
  obtain ⟨iW, hiW⟩ := GlobalTheory.T.exists_unitary_hom_frame_conjugation_at_place F E σ v (a + a') G.W L σL δ ι hδne him hmul hσ PW JT hJTg
  have hlat := GlobalTheory.T.mem_tensorLatticeAtPlace_iff_frame_coordinates_integral F E v a (a + a') G.V G.W L ι hinj him hmul hint PV PW hPV hPW
  have e1 : ∀ M : Matrix (Fin a) (Fin (a + a')) L,
      ((PV⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * ((PV : Matrix (Fin a) (Fin a) L) * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have e2 : ∀ M : Matrix (Fin (a + a')) (Fin (a + a')) L,
      (PW : Matrix (Fin (a + a')) (Fin (a + a')) L)ᵀ *
        (((PW⁻¹ : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L)ᵀ * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one, Matrix.one_mul]
  refine ⟨JS, JT, GlobalTheory.InertLocFrame.xm ι PV PW, iV, iW, hJS, hJT, hJSh, hJTh,
    GlobalTheory.T.weil_symplectic_form_frame_coordinates_eq_local_trace F E σ B v a (a + a') G.V G.W L ϖ σL q δ ψL ι hunr hδ hinj him hmul hσ hψ PV JS PW JT hJSg hJTg,
    GlobalTheory.T.supported_matrix_iff_frame_coordinates_of_inert F E v a (a + a') L ι hinj him hmul PV PW, fun u hu => (hlat _).2 ⟨u, hu, rfl⟩,
    fun z hz => (hlat z).1 hz, ?_, fun g => GlobalTheory.T.supported_adelic_unitary_point_of_local_matrix F E σ v a G.V L ι him (iV g) _ (hiV g),
    fun h => GlobalTheory.T.supported_adelic_unitary_point_of_local_matrix F E σ v (a + a') G.W L ι him (iW h) _ (hiW h), ?_, ?_⟩
  · intro g h x
    rw [GlobalTheory.T.frame_coordinates_action_of_identity_off_place F E σ a (a + a') G.V G.W L ι hmul PV PW _ _ (iV g) (iW h) (hiV g) (hiW h) x,
      GlobalTheory.InertLocFrame.xm_apply]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, e1, e2]
  · intro g hg
    refine GlobalTheory.T.mem_latticeStabilizer_of_frame_conj_integral F E σ v a G.V L ι hinj him hmul hint PV hPV (iV g)
      (((g : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)ᵀ ((g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)ᵀ
      (fun i j => ent _ (inv_mem hg) j i) (fun i j => ent _ hg j i) (hiV g) ?_
    rw [← map_inv, hiV, Subgroup.coe_inv, inv_inv]
  · intro h hh
    refine GlobalTheory.T.mem_latticeStabilizer_of_frame_conj_integral F E σ v (a + a') G.W L ι hinj him hmul hint PW hPW (iW h)
      ((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L)
      (((h : GL (Fin (a + a')) L)⁻¹ : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L)
      (fun i j => ent _ hh i j) (fun i j => ent _ (inv_mem hh) i j) (hiW h) ?_
    rw [← map_inv, hiW, Subgroup.coe_inv]
