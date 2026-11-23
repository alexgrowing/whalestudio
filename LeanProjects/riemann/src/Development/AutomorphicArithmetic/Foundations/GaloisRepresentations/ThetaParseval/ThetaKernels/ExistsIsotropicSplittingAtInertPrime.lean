import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.BumpLat
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA
section
open PositivityTheory.ThKH.Iwas GlobalTheory.LFun GlobalTheory.LFun.InertChart Formalism.UG PositivityTheory.ThK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
  {w : HeightOneSpectrum (𝓞 E)}
private theorem sgE_mem_Oh_pk {y : TensorProduct F (Fv F v) E} (hy : y ∈ intLoc F E v) : sgE E v y ∈ Oh E v := by
  refine intLoc_induction (p := fun y => sgE E v y ∈ Oh E v) (fun a ha x => ?_) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · refine AddSubgroup.subset_closure ⟨PositivityTheory.ThKH.Iwas.sg v a, at_sg a, by rwa [ev_sg], x, ?_⟩
    change TensorProduct.tmul F (PositivityTheory.ThKH.Iwas.sg v a) (x : E) = TensorProduct.tmul F (PositivityTheory.ThKH.Iwas.sg v a * 1) (x : E)
    rw [mul_one]
  · rw [map_zero]; exact zero_mem _
  · rw [map_add]; exact add_mem hy hz
  · rw [map_neg]; exact neg_mem hy
private theorem sg_one_smul_pk {x : AE F E} (hx : At (evFin F v) x) : PositivityTheory.ThKH.Iwas.sg v 1 • x = x := by
  have h1 := hx (1 - PositivityTheory.ThKH.Iwas.sg v 1) (by rw [map_sub, map_one, ev_sg, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm
private theorem mem_Oh_pk (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {x : AE F E} (hx : At (evFin F v) x)
    (hi : piE h x ∈ Ov E w) : x ∈ Oh E v := by
  rw [← sg_one_smul_pk hx, ← sgE_comp]
  exact sgE_mem_Oh_pk ((mem_intLoc_iff hw h _).2 hi)
private theorem piE_sg_smul_pk (h : w.under (𝓞 F) = v) (x : AE F E) : piE h (PositivityTheory.ThKH.Iwas.sg v 1 • x) = piE h x := by
  rw [← sgE_comp]
  change toCompl h (compFin F E v (sgE E v _)) = _
  rw [comp_sgE]
  rfl
private theorem piE_eM_pk (h : w.under (𝓞 F) = v) (n : ℕ) : (eM (E := E) v n).map (piE h) = 1 := by
  refine Matrix.ext fun i j => ?_
  change piE h (PositivityTheory.ThKH.Iwas.sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) = _
  rw [piE_sg_smul_pk, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp
private theorem at_eM_pk (n : ℕ) : At (evFin F v) (eM (E := E) v n) := fun u hu => by
  change u • (PositivityTheory.ThKH.Iwas.sg v 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) = 0
  rw [smul_smul, ← smul_eq_mul, at_sg 1 u hu, zero_smul]
theorem exists_isoW_k {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {W : Spc F E d} {r s : ℕ} (hB : _root_.UpperTheory.TP.W.GoodK σ B)
    (hW : W.IsSkew σ B r s) (h2 : 2 * n ≤ d) (hw : IsInertAt F E v w) : ∃ Y R, IsIsoW σ W v (n := n) Y R := by
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨a, ha, l, -, hg⟩ := exists_frame hB.cm hw h hc hW
  let f : Fin n → Fin d := Fin.castLE (by omega)
  have hf : Function.Injective f := Fin.castLE_injective _
  obtain ⟨Y, hY, eY⟩ := mat_surj h (a.1ᵀ.submatrix f id)
  obtain ⟨R, hR, eR⟩ := mat_surj h ((a⁻¹).1ᵀ.submatrix id f)
  refine ⟨Y, R, fun i => ?_, ?_, ?_, fun z hz j => ?_⟩
  · refine (mem_latW_iff hw h W _).2 ⟨fun u hu => congrFun (hY u hu) i, ?_⟩
    have e : piE h ∘ Y i = a.1 *ᵥ fun k => (1 : Matrix (Fin d) (Fin d) (w.adicCompletion E)) k (f i) := by
      funext k
      have e1 : piE h (Y i k) = a.1 k (f i) := congrFun (congrFun eY i) k
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, e1]
    rw [e]
    exact (ha _).1 fun k => one_int k (f i)
  · refine mat_inj hw h (at_sub (at_mul_left hY _) (at_eM_pk n)) ?_
    rw [Matrix.map_mul, eY, eR, piE_eM_pk]
    have e : a.1ᵀ.submatrix f id * (a⁻¹).1ᵀ.submatrix id f = (a.1ᵀ * (a⁻¹).1ᵀ).submatrix f f := rfl
    rw [e, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.submatrix_one _ hf]
  · refine mat_inj hw h (at_sub (at_mul_left (at_mul_left hY _) _) at_zero) ?_
    have e := map_gram hc W.J Yᵀ Yᵀ
    rw [Matrix.transpose_transpose] at e
    have e2 : Yᵀ.map (piE h) = a.1.submatrix id f := by
      rw [Matrix.transpose_map, eY]; rfl
    rw [e2] at e
    refine e.trans (Matrix.ext fun i j => ?_)
    have e3 := congrFun (congrFun hg (f i)) (f j)
    refine e3.trans ?_
    have := i.2; have := j.2
    have e4 : (f i : ℕ) = i := rfl
    have e5 : (f j : ℕ) = j := rfl
    rw [Matrix.smul_apply]
    simp only [antiJ, Matrix.of_apply]
    rw [if_neg (by omega)]
    simp
  · obtain ⟨h3, h4⟩ := (mem_latW_iff hw h W z).1 hz
    rw [← Matrix.mulVec_transpose]
    refine mem_Oh_pk hw h (fun u hu => congrFun (at_mulVec_left (at_transpose hR) z u hu) j) ?_
    have e := congrFun (piE_mulVec h Rᵀ z) j
    rw [Function.comp_apply] at e
    rw [e]
    have e2 : Rᵀ.map (piE h) = (a⁻¹).1.submatrix f id := by
      rw [Matrix.transpose_map, eR]; rfl
    rw [e2]
    exact coord_int ha h4 (f j)
end
theorem UpperTheory.exists_isotropic_splitting_at_inert_prime :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (W : Spc F E d) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → W.IsSkew σ B r s → 2 * n ≤ d → ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∃ Y R, IsIsoW σ W v (n := n) Y R := by
  intro F E _ _ _ _ _ σ B n d W r s hB hW h2 v w hw
  exact _root_.exists_isoW_k hB hW h2 hw
end
