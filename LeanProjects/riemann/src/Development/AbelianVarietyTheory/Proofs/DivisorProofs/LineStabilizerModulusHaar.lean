import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLineStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerHaarLocalFactorCaseB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSignatureDropsByPlane
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.IwasawaKAvgInt

noncomputable section

namespace GlobalTheory.ArchLineModulus

theorem map_mul_right_of_retract {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
    [MeasurableSpace A] [BorelSpace A] (j : A →* G) (r : G →* A) (hj : Continuous j) (hr : Continuous r)
    (hrj : ∀ a, r (j a) = a) (hc : ∀ a k, r k = 1 → Commute (j a) k) (μ : Measure A) [μ.IsHaarMeasure] (a : A) :
    μ.map (· * a) = Measure.modularCharacterFun (j a) • μ := by
  borelize G
  have hK : IsClosed ((r.ker : Subgroup G) : Set G) := isClosed_eq hr continuous_const
  haveI : LocallyCompactSpace r.ker := hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology r.ker := TopologicalSpace.Subtype.secondCountableTopology _
  have hmem : ∀ g, (j (r g))⁻¹ * g ∈ r.ker := fun g => by simp [MonoidHom.mem_ker, hrj]
  let e : (A × r.ker) ≃ₜ* G :=
    { toFun := fun p => j p.1 * p.2
      invFun := fun g => (r g, ⟨(j (r g))⁻¹ * g, hmem g⟩)
      left_inv := fun p => by
        have h : r (p.2 : G) = 1 := p.2.2
        refine Prod.ext ?_ (Subtype.ext ?_) <;> simp [hrj, h]
      right_inv := fun g => by simp
      map_mul' := fun p q => by
        have h := (hc q.1 p.2 p.2.2).eq
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Subgroup.coe_mul]
        rw [mul_assoc, mul_assoc, ← mul_assoc (j q.1), h, mul_assoc]
      continuous_toFun := (hj.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := hr.prodMk (Continuous.subtype_mk
        (show Continuous fun g => (j (r g))⁻¹ * g from (hj.comp hr).inv.mul continuous_id) hmem) }
  let κ : Measure r.ker := Measure.haar
  let ν : Measure G := (μ.prod κ).map e
  haveI : (μ.prod κ).IsHaarMeasure := Measure.prod.instIsHaarMeasure μ κ
  haveI : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ e
  have hem : Measurable e := e.continuous.measurable
  have h1 : μ.map (· * a) = Measure.modularCharacterFun a • μ := Measure.map_right_mul_eq_modularCharacterFun_smul μ a
  have h2 : ν.map (· * j a) = Measure.modularCharacterFun (j a) • ν :=
    Measure.map_right_mul_eq_modularCharacterFun_smul ν (j a)
  have h3 : ν.map (· * j a) = Measure.modularCharacterFun a • ν := by
    have hcomp : (· * j a) ∘ e = e ∘ Prod.map (· * a) id := by
      funext p
      have : e (a, 1) = j a := by show j a * ((1 : r.ker) : G) = j a; simp
      simp only [Function.comp_apply]
      rw [← this, ← map_mul]
      congr 1
      ext <;> simp
    simp only [ν]
    rw [Measure.map_map (measurable_mul_const _) hem, hcomp,
      ← Measure.map_map hem ((measurable_mul_const a).prodMap measurable_id),
      ← Measure.map_prod_map _ _ (measurable_mul_const a) measurable_id, h1, Measure.map_id, ENNReal.smul_def,
      Measure.prod_smul_left, Measure.map_smul, ENNReal.smul_def]
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : ν C ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hC1).ne'
  have hfin : ν C ≠ ⊤ := hC.measure_lt_top.ne
  have h4 := congrArg (fun m : Measure G => m C) (h2.symm.trans h3)
  simp only [Measure.coe_nnreal_smul_apply] at h4
  have h5 : Measure.modularCharacterFun (j a) = Measure.modularCharacterFun a := by
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h4
  rw [h1, h5]

open GlobalTheory.ThK.ConeEuler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem compArch_of_mem {X : Spc F E n} {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) : compArch σ X.J g = g := by
  refine Subtype.ext (Units.ext ?_)
  have h : (1 - eInf F) • (mat g - 1) = 0 :=
    hg _ (by rw [eInf, GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, evI_realAd_one, sub_self])
  change eInf F • mat g + (1 - eInf F) • 1 = mat g
  rw [smul_sub, sub_eq_zero] at h
  rw [← h, ← add_smul, add_sub_cancel, one_smul]

theorem commute_compArch {J : Matrix (Fin n) (Fin n) E} (x y : UA σ J) (hx : compArch σ J x = 1) :
    Commute (compArch σ J y) x := by
  have hε := eInf_idem (F := F)
  have h1 := idem_mul_one_sub hε
  have h2 := one_sub_idem hε
  have e : mat ((compArch σ J x)⁻¹ * x) = eInf F • 1 + (1 - eInf F) • mat x := by
    rw [← map_inv, GlobalTheory.StabHaar.mat_mul, mat_compArch, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mul]
  rw [hx, inv_one, one_mul] at e
  refine Subtype.ext (Units.ext ?_)
  change mat (compArch σ J y) * mat x = mat x * mat (compArch σ J y)
  rw [e, mat_compArch]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add,
    smul_smul, hε, h1, h2, mul_comm (1 - eInf F) (eInf F), zero_smul, add_zero, zero_add]

theorem compArch_line {J : Matrix (Fin n) (Fin n) E} {x : Fin n → E} {q : UA σ J} {a : (AE F E)ˣ}
    (h : mat q *ᵥ incV F x = (a : AE F E) • incV F x) :
    mat (compArch σ J q) *ᵥ incV F x = (unitArch F E a : AE F E) • incV F x := by
  rw [mat_compArch, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h]
  show _ = (eInf F • (a : AE F E) + (1 - eInf F) • (1 : AE F E)) • incV F x
  rw [add_smul, smul_assoc, smul_assoc, one_smul]

set_option synthInstance.maxHeartbeats 400000 in

theorem map_mul_right_lineStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n₁ : ℕ) (X : Spc F E (n₁ + 2)) (X₁ : Spc F E n₁) (H : Plane E (n₁ + 2) n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ μP : Measure (lineStab σ X H.x), μP.IsHaarMeasure → ∀ (p : lineStab σ X H.x) (t : (AE F E)ˣ),
      mat p.1.1 *ᵥ incV F H.x = t.1 • incV F H.x → μP.map (· * p) = (absE F E t ^ (n₁ + 1)) • μP := by
  intro F E _ _ _ _ _ σ B n₁ X X₁ H i₀ i₁ r s hB hX hH μP hμ p t ht
  have hX₁ := GlobalTheory.isHerm_plane_complement F E σ B hB _ _ X X₁ H i₀ i₁ r s hX hH
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ _ X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨m, hm⟩ := GlobalTheory.IwKInt.levi_section hB hX hX₁ hH
  obtain ⟨-, -, -, -, hQc, -, -, -⟩ :=
    GlobalTheory.LeviSec.leviSection_props F E σ B _ _ X X₁ r s _ _ i₀ i₁ H hB hX hX₁ hH m hm
  haveI : LocallyCompactSpace (GlobalTheory.IwLine.lineStab σ X.J H.x) := hQc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (GlobalTheory.IwLine.lineStab σ X.J H.x) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (UAtSub σ X (evI F)) :=
    (isClosed_UAtSub X (evI F)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (UAtSub σ X (evI F)) := TopologicalSpace.Subtype.secondCountableTopology _
  have hPc : IsClosed ((lineStab σ X H.x : Subgroup _) : Set (UAtSub σ X (evI F))) :=
    hQc.preimage continuous_subtype_val
  haveI : LocallyCompactSpace (lineStab σ X H.x) := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (lineStab σ X H.x) := TopologicalSpace.Subtype.secondCountableTopology _
  let j : lineStab σ X H.x →* GlobalTheory.IwLine.lineStab σ X.J H.x :=
    { toFun := fun q => ⟨q.1.1, q.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ρ : GlobalTheory.IwLine.lineStab σ X.J H.x →* lineStab σ X H.x :=
    { toFun := fun q => ⟨⟨compArch σ X.J q.1, compArch_mem q.1⟩, ⟨_, compArch_line q.2.choose_spec⟩⟩
      map_one' := Subtype.ext (Subtype.ext (map_one (compArch σ X.J)))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (map_mul (compArch σ X.J) a.1 b.1)) }
  have hj : Continuous j := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hρ : Continuous ρ :=
    (((continuous_components F E σ _ X.J).2.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  have hρj : ∀ a, ρ (j a) = a := fun a => Subtype.ext (Subtype.ext (compArch_of_mem a.1.2))
  have hc : ∀ a k, ρ k = 1 → Commute (j a) k := fun a k hk => by
    have hk' : compArch σ X.J k.1 = 1 := congrArg (fun z : lineStab σ X H.x => z.1.1) hk
    have h := commute_compArch k.1 a.1.1 hk'
    rw [compArch_of_mem a.1.2] at h
    exact Subtype.ext h.eq
  rw [map_mul_right_of_retract j ρ hj hρ hρj hc μP p, GlobalTheory.IwKInt.modular_lineStab hB hX hX₁ hH (j p) ht]

end GlobalTheory.ArchLineModulus

end
