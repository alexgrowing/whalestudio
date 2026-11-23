import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.KLevTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.CongruenceExistence

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private theorem memK {w : Plc L} (h : GL (Fin n) (Kw w)) : h ∈ GlobalTheory.LFun.KGL w n ↔
    (∀ i j, h.1 i j ∈ w.adicCompletionIntegers L) ∧ ∀ i j, (h⁻¹).1 i j ∈ w.adicCompletionIntegers L := by
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]; rfl

private theorem memO {x : Af L} : x ∈ UpperTheory.V.Af.Ohat L ↔ ∀ w : Plc L, pLoc L w x ∈ w.adicCompletionIntegers L := by
  rw [UpperTheory.V.Af.Ohat, Subring.mem_iInf]; rfl

private def fp : UA L n →* GL (Fin n) (Af L) :=
  (Matrix.GeneralLinearGroup.map (pFin L)).comp (UA L n).subtype

private theorem cLoc_val (w : Plc L) (x : UA L n) (i j : Fin n) :
    (cLoc w x).1 i j = pLoc L w ((fp x).1 i j) := rfl

private theorem cLoc_inv_val (w : Plc L) (x : UA L n) (i j : Fin n) :
    ((cLoc w x)⁻¹).1 i j = pLoc L w (((fp x)⁻¹).1 i j) := by
  rw [← map_inv, ← map_inv]; rfl

private theorem pLoc_one (w : Plc L) (i j : Fin n) :
    pLoc L w ((1 : Matrix (Fin n) (Fin n) (Af L)) i j) = (1 : Matrix (Fin n) (Fin n) (Kw w)) i j := by
  simp only [Matrix.one_apply]; split_ifs <;> simp

private theorem mem_iff {m : ℕ} (hm : m ≠ 0) (x : UA L n) :
    (x ∈ finU L n ∧ fp x ∈ UpperTheory.V.Af.KLev L n m) ↔
      x ∈ Kall L n ∧ ∀ w i j, ∃ a ∈ w.adicCompletionIntegers L, (mL w x - 1) i j = (m : Kw w) * a := by
  have hd : ∀ (w : Plc L) (i j : Fin n), (mL w x - 1) i j =
      pLoc L w ((fp x).1 i j - (1 : Matrix (Fin n) (Fin n) (Af L)) i j) := fun w i j => by
    rw [map_sub, pLoc_one, Matrix.sub_apply]; rfl
  constructor
  · rintro ⟨hf, hk⟩
    obtain ⟨h1, h2, h3⟩ := UpperTheory.V.Af.mem_KLev.1 hk
    refine ⟨⟨hf, Subgroup.mem_iInf.2 fun w => (memK _).2 ⟨fun i j => ?_, fun i j => ?_⟩⟩, fun w i j => ?_⟩
    · rw [cLoc_val]; exact memO.1 (h1 i j) w
    · rw [cLoc_inv_val]; exact memO.1 (h2 i j) w
    · obtain ⟨y, hy, e⟩ := h3 i j
      refine ⟨pLoc L w y, memO.1 hy w, ?_⟩
      rw [hd, show (fp x).1 i j - (1 : Matrix (Fin n) (Fin n) (Af L)) i j = (m : Af L) * y from e, map_mul, map_natCast]
  · rintro ⟨⟨hf, hK⟩, hc⟩
    have hK' : ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w n := fun w => Subgroup.mem_iInf.1 hK w
    have hm' : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm
    set u : Af L := algebraMap L (Af L) (m : L)⁻¹ with hu'
    have hu : u * (m : Af L) = 1 := by
      rw [hu', ← map_natCast (algebraMap L (Af L)), ← map_mul, inv_mul_cancel₀ hm', map_one]
    refine ⟨hf, UpperTheory.V.Af.mem_KLev.2 ⟨fun i j => memO.2 fun w => ?_, fun i j => memO.2 fun w => ?_, fun i j =>
      ⟨u * ((fp x).1 i j - (1 : Matrix (Fin n) (Fin n) (Af L)) i j), memO.2 fun w => ?_, ?_⟩⟩⟩
    · rw [← cLoc_val]; exact ((memK _).1 (hK' w)).1 i j
    · rw [← cLoc_inv_val]; exact ((memK _).1 (hK' w)).2 i j
    · obtain ⟨a, ha, e⟩ := hc w i j
      rw [map_mul, ← hd, e, ← mul_assoc]
      have : pLoc L w u * (m : Kw w) = 1 := by
        have := congrArg (pLoc L w) hu
        rwa [map_mul, map_natCast, map_one] at this
      rwa [this, one_mul]
    · rw [← mul_assoc, mul_comm _ u, hu, one_mul]

private def cong (m : ℕ) : Subgroup (UA L n) := finU L n ⊓ (UpperTheory.V.Af.KLev L n m).comap fp

private theorem isCong {m : ℕ} (hm : m ≠ 0) : IsCong m (cong (L := L) (n := n) m) := fun x => mem_iff hm x

private theorem isLevel {m : ℕ} (hm : m ≠ 0) : IsLevel (cong (L := L) (n := n) m) := by
  refine ⟨fun x hx => ((isCong hm x).1 hx).1, ?_⟩
  have hc : Continuous fun x : finU L n => fp (x : UA L n) :=
    GlobalTheory.CuspRep.continuous_mapFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  convert (UpperTheory.V.Af.isOpen_KLev (F := L) (n := n) (M := m) (Nat.one_le_iff_ne_zero.2 hm)).preimage hc using 1
  ext x
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

private theorem trans_int {w : Plc L} {i j : Fin n} {c : Kw w} (hc : c ∈ w.adicCompletionIntegers L) (a b : Fin n) :
    Matrix.transvection i j c a b ∈ w.adicCompletionIntegers L := by
  rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  refine add_mem ?_ ?_
  · split_ifs
    · exact one_mem _
    · exact zero_mem _
  · split_ifs
    · exact hc
    · exact zero_mem _

private def el {w : Plc L} {i j : Fin n} (h : i ≠ j) : GL (Fin n) (Kw w) :=
  ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩

private theorem el_mem {w : Plc L} {i j : Fin n} (h : i ≠ j) : el (w := w) h ∈ GlobalTheory.LFun.KGL w n :=
  (memK _).2 ⟨fun a b => trans_int (one_mem _) a b, fun a b => trans_int (neg_mem (one_mem _)) a b⟩

private theorem last {m : ℕ} (hn : 2 ≤ n) (w : Plc L) (hw : IsSplitAt w)
    (hle : locU n w ⊓ Kall L n ≤ cong (L := L) (n := n) m) (hm : m ≠ 0) : (m : 𝓞 L) ∉ w.asIdeal := by
  intro hmw
  obtain ⟨h1, -, -, -, -, -, -, h8⟩ := UpperTheory.V.Z.Sym.Dict.Br.uaFacts L n
  obtain ⟨hl, hc, -, -⟩ := h1 w hw
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set g : GL (Fin n) (Kw w) := el hij with hg
  have hx := hl g
  have hK : secW n w g ∈ Kall L n := by
    refine ⟨hx.1, Subgroup.mem_iInf.2 fun u => ?_⟩
    by_cases hu : un u = un w
    · refine h8 w hw _ ?_ u hu
      rw [hc]; exact el_mem hij
    · have : secW n w g ∈ (cLoc (E := L) (n := n) u).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 u) hu
      exact Subgroup.mem_comap.2 (by rw [MonoidHom.mem_ker.1 this]; exact one_mem _)
  obtain ⟨a, ha, e⟩ := ((isCong hm _).1 (hle ⟨hx, hK⟩)).2 w ⟨0, by omega⟩ ⟨1, by omega⟩
  have e1 : (mL w (secW n w g) - 1) ⟨0, by omega⟩ ⟨1, by omega⟩ = 1 := by
    rw [mL, hc]
    simp [g, el, Matrix.transvection, Matrix.single_apply]
  rw [e1] at e
  have hv : Valued.v ((m : Kw w)) < 1 := by
    have h0 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w (m : 𝓞 L)).2 hmw
    have e2 : (m : Kw w) = algebraMap L (Kw w) (algebraMap (𝓞 L) L (m : 𝓞 L)) := by simp
    rw [e2]
    first
      | (rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact h0)
      | (rw [HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.valuedAdicCompletion_eq_valuation]; exact h0)
      | (erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact h0)
  have ha' : Valued.v a ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ha
  have := congrArg Valued.v e
  rw [map_one, map_mul] at this
  have h3 : Valued.v (m : Kw w) * Valued.v a < 1 := by
    calc _ ≤ Valued.v (m : Kw w) * 1 := by gcongr
      _ < 1 := by simpa using hv
  exact absurd this h3.ne'

end UpperTheory.V.Z.Sym.So.CongruenceExistence

open UpperTheory.V.Z.Sym.So.CongruenceExistence in
theorem UpperTheory.V.Z.Sym.So.congEx :
    UpperTheory.V.Z.Sym.So.CongEx := by
  intro L _ _ _ n m hm
  exact ⟨cong m, isCong hm, isLevel hm, fun hn w hw hle => last hn w hw hle hm⟩

end
