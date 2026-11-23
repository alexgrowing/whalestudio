import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.LevChr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_sub_lt {m : Type} [Fintype m] [DecidableEq m] {A B : Matrix m m k} (hA : IntM A) (hB : IntM B)
    (h : MaxM (A - B)) : valuation k (A.det - B.det) < 1 := by
  let A' : Matrix m m 𝒪[k] := fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix m m 𝒪[k] := fun i j => ⟨B i j, hB i j⟩
  have eA : A.det = ((A'.det : 𝒪[k]) : k) := by
    change _ = (algebraMap 𝒪[k] k) A'.det
    rw [RingHom.map_det]; rfl
  have eB : B.det = ((B'.det : 𝒪[k]) : k) := by
    change _ = (algebraMap 𝒪[k] k) B'.det
    rw [RingHom.map_det]; rfl
  rw [eA, eB, ← residue_eq_iff_lt, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  exact (residue_eq_iff_lt (A' i j) (B' i j)).2 (by simpa using h i j)

end GlobalTheory.LevChr

namespace GlobalTheory.LevChr

theorem secondBlockIndex_eq_one_iff_basisNumbering {K s T j n : ℕ} {e : StepData.Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) (a : Fin n) :
    Formalism.L2.DIV.blk2 (K + (s + 1)) a = 1 ↔ ∃ p, e.symm a = .inr p := by
  have h0 := he (e.symm a)
  rw [e.apply_symm_apply] at h0
  have hb : Formalism.L2.DIV.blk2 (K + (s + 1)) a = 1 ↔ ¬ a.val < K + (s + 1) := by
    unfold Formalism.L2.DIV.blk2; split_ifs with h <;> simp [h]
  rw [hb]
  rcases hc : e.symm a with (i | i) | p <;> rw [hc] at h0 <;> simp only [GlobalTheory.SymBridge.zPos] at h0
  · have := i.2; simp; omega
  · have := i.2; simp; omega
  · simp; omega

end GlobalTheory.LevChr

theorem GlobalTheory.LevChr.lam_eq_inv_xi : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → (∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (ξ : (𝓞 E ⧸ PP.asIdeal)ˣ →* ℂˣ), (∀ (z : 𝓞 E) (u : kˣ) (r : (𝓞 E ⧸ PP.asIdeal)ˣ), (u : k) = ι z → (r : 𝓞 E ⧸ PP.asIdeal) = Ideal.Quotient.mk PP.asIdeal z → δ u = (ξ r)⁻¹) → ∀ (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k) (hx : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) → (ξ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R))⁻¹ = ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).lam ⟨x, hx⟩ := by
  intro E _ _ k _ _ _ _ PP ι _h1 _h2 K T s j d hd δ hδ η ξ hRes n e he x hx R hR hTri
  have hx' : (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x ∈
      (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).J := hx
  change _ = (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).lam ⟨_, hx'⟩
  obtain ⟨hKO, hC⟩ := mem_parahoric.1 hx'
  obtain ⟨-, D, hD, hDv⟩ := exists_diag_blocks hKO hC
  rw [parahoric_lam ⟨_, hx'⟩ D hDv]
  have hy : ((plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x).val =
      x.val.submatrix (stdOrd (Fin K) (Fin T) j d hd) (stdOrd (Fin K) (Fin T) j d hd) := by
    change ((reGL (stdOrd (Fin K) (Fin T) j d hd)).symm
      ((MulAut.conj (1 : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k)).symm x)).val = _
    rw [reGL_symm_val, MulAut.conj_symm_apply]
    simp
  have hDe : ∀ p p', D.val p p' =
      x.val (stdOrd (Fin K) (Fin T) j d hd (.inr p)) (stdOrd (Fin K) (Fin T) j d hd (.inr p')) := by
    intro p p'; rw [hDv, hy]; rfl

  have hb := GlobalTheory.LevChr.secondBlockIndex_eq_one_iff_basisNumbering he
  let f : Fin j × Fin T ≃ {a : Fin n // Formalism.L2.DIV.blk2 (K + (s + 1)) a = 1} :=
    Equiv.ofBijective (fun p => ⟨e (.inr p), (hb _).2 ⟨p, by simp⟩⟩)
      ⟨fun p p' h => Sum.inr_injective (e.injective (congrArg Subtype.val h)), fun a => by
        obtain ⟨p, hp⟩ := (hb a.1).1 a.2
        exact ⟨p, Subtype.ext (by simp [← hp])⟩⟩

  choose Z hZ using fun a a' => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (R.val a a')
  let Zf : Matrix (Fin j × Fin T) (Fin j × Fin T) (𝓞 E) := fun p p' => Z (e (.inr p)) (e (.inr p'))
  have hdet : ((Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R : (𝓞 E ⧸ PP.asIdeal)ˣ) : 𝓞 E ⧸ PP.asIdeal) =
      Ideal.Quotient.mk PP.asIdeal Zf.det := by
    rw [Formalism.L2.DIV.diag_block_det_val 1 hTri, ← Matrix.det_submatrix_equiv_self f, RingHom.map_det]
    congr 1
    ext p p'
    show R.val (e (.inr p)) (e (.inr p')) = Ideal.Quotient.mk PP.asIdeal (Z (e (.inr p)) (e (.inr p')))
    rw [hZ]

  have hA : IntM D.val := intM_of_mem_KO hD
  have hM : MaxM (D.val - (ι.comp (algebraMap (𝓞 E) E)).mapMatrix Zf) := fun p p' => by
    have h := hR (e (.inr p)) (e (.inr p')) _ (hZ _ _).symm
    simp only [Equiv.symm_apply_apply] at h
    show valuation k (D.val p p' - ι (Z (e (.inr p)) (e (.inr p')) : E)) < 1
    rw [hDe]; exact h
  have hB : IntM ((ι.comp (algebraMap (𝓞 E) E)).mapMatrix Zf) := fun p p' => by
    have h := sub_mem (hA p p') (hM.intM p p')
    simpa using h
  have hlt := GlobalTheory.LevChr.det_sub_lt hA hB hM
  rw [← RingHom.map_det] at hlt
  have hlt' : valuation k (((Matrix.GeneralLinearGroup.det D : kˣ) : k) - ι (Zf.det : E)) < 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hlt
  have hv1 : valuation k ((Matrix.GeneralLinearGroup.det D : kˣ) : k) = 1 := valuation_det_of_mem_KO hD
  have hvz : valuation k (ι (Zf.det : E)) = 1 := by
    have h : valuation k (ι (Zf.det : E) - (Matrix.GeneralLinearGroup.det D : kˣ)) <
        valuation k ((Matrix.GeneralLinearGroup.det D : kˣ) : k) := by
      rw [hv1, ← Valuation.map_neg, neg_sub]; exact hlt'
    rw [Valuation.map_eq_of_sub_lt _ h, hv1]
  have hz0 : ι (Zf.det : E) ≠ 0 := by
    intro h; rw [h, map_zero] at hvz; exact zero_ne_one hvz
  set u : kˣ := Units.mk0 (ι (Zf.det : E)) hz0 with hu
  have htame : δ (u⁻¹ * Matrix.GeneralLinearGroup.det D) = 1 := by
    apply hδ
    have e1 : ((u⁻¹ * Matrix.GeneralLinearGroup.det D : kˣ) : k) - 1 =
        (ι (Zf.det : E))⁻¹ * (((Matrix.GeneralLinearGroup.det D : kˣ) : k) - ι (Zf.det : E)) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hu, Units.val_mk0, mul_sub, inv_mul_cancel₀ hz0]
    rw [e1, map_mul, map_inv₀, hvz, inv_one, one_mul]; exact hlt'
  rw [show Matrix.GeneralLinearGroup.det D = u * (u⁻¹ * Matrix.GeneralLinearGroup.det D) by group, map_mul, htame,
    mul_one]
  exact (hRes Zf.det u _ (by rw [hu, Units.val_mk0]) hdet).symm
