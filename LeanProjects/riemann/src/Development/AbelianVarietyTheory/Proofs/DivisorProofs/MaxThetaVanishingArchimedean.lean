import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalProductFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThKLocSS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def infOne : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def finOne : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

theorem infOne_add_finOne : (infOne : AF F) + finOne = 1 := by
  show ((1 + 0 : InfiniteAdeleRing F), (0 + 1 : FiniteAdeleRing (𝓞 F) F)) = ((1, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  simp

theorem infOne_mul_finOne : (infOne : AF F) * finOne = 0 := by
  show ((1 * 0 : InfiniteAdeleRing F), (0 * 1 : FiniteAdeleRing (𝓞 F) F)) = ((0, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  simp

theorem finOne_mul_infOne : (finOne : AF F) * infOne = 0 := by
  show ((0 * 1 : InfiniteAdeleRing F), (1 * 0 : FiniteAdeleRing (𝓞 F) F)) = ((0, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  simp

theorem evFin_one_zero (v : Pl F) : evFin F v (infOne : AF F) = 0 := by
  show evalV F v (0 : FiniteAdeleRing (𝓞 F) F) = 0
  exact map_zero _

theorem evI_zero_one : evI F (finOne : AF F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem commute_of_evI_evFin {d : ℕ} {W : Spc F E d} (v : Pl F) {k h : UA σ W.J}
    (hk : k ∈ UAt σ W (evI F)) (hh : h ∈ UAt σ W (evFin F v)) : k * h = h * k := by
  set A := mat k - 1
  set C := mat h - 1
  have hA : A = (infOne : AF F) • A := by
    have h0 : (finOne : AF F) • A = 0 := hk _ evI_zero_one
    have e : (infOne : AF F) + finOne = 1 := infOne_add_finOne
    calc A = ((infOne : AF F) + finOne) • A := by rw [e, one_smul]
      _ = (infOne : AF F) • A := by rw [add_smul, h0, add_zero]
  have hC : C = (finOne : AF F) • C := by
    have h0 : (infOne : AF F) • C = 0 := hh _ (evFin_one_zero v)
    have e : (infOne : AF F) + finOne = 1 := infOne_add_finOne
    calc C = ((infOne : AF F) + finOne) • C := by rw [e, one_smul]
      _ = (finOne : AF F) • C := by rw [add_smul, h0, zero_add]
  have e0 : (infOne : AF F) * finOne = 0 := infOne_mul_finOne
  have e0' : (finOne : AF F) * infOne = 0 := finOne_mul_infOne
  have hAC : A * C = 0 := by
    rw [hA, hC, Matrix.smul_mul, Matrix.mul_smul, smul_smul, e0, zero_smul]
  have hCA : C * A = 0 := by
    rw [hA, hC, Matrix.smul_mul, Matrix.mul_smul, smul_smul, e0', zero_smul]
  have hk' : mat k = 1 + A := by simp [A]
  have hh' : mat h = 1 + C := by simp [C]
  have hm : mat k * mat h = mat h * mat k := by
    rw [hk', hh']
    simp only [add_mul, mul_add, one_mul, mul_one, hAC, hCA]
    abel
  exact Subtype.ext (Units.ext hm)

theorem isSimpleOver_map {V : Type} [AddCommGroup V] [Module ℂ V] {T : Set (Module.End ℂ V)} {N S : Submodule ℂ V}
    (f g : Module.End ℂ V) (hfg : f * g = 1) (hgf : g * f = 1) (hfN : N.map f ≤ N) (hgN : N.map g ≤ N)
    (hfT : ∀ t ∈ T, t * f = f * t) (hgT : ∀ t ∈ T, t * g = g * t) (hS : IsSimpleOver T N S) :
    IsSimpleOver T N (S.map f) := by
  have mfg : ∀ P : Submodule ℂ V, (P.map g).map f = P := fun P => by
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, hfg, Module.End.one_eq_id, Submodule.map_id]
  have mgf : ∀ P : Submodule ℂ V, (P.map f).map g = P := fun P => by
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, hgf, Module.End.one_eq_id, Submodule.map_id]
  have stab : ∀ (h : Module.End ℂ V), (∀ t ∈ T, t * h = h * t) → ∀ P, OpStable T P → OpStable T (P.map h) := by
    rintro h hh P hP t ht _ ⟨x, hx, rfl⟩
    refine ⟨t x, hP t ht x hx, ?_⟩
    change h (t x) = t (h x)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hh t ht]
  obtain ⟨hlt, hst, hmax⟩ := hS
  have hNS : N ≤ S.map f := by
    calc N = (N.map g).map f := (mfg N).symm
      _ ≤ S.map f := Submodule.map_mono (hgN.trans hlt.le)
  refine ⟨lt_of_le_of_ne hNS fun h => hlt.ne ?_, stab f hfT S hst, fun S' hNS' hS'S hS' => ?_⟩
  · apply le_antisymm hlt.le
    calc S = (S.map f).map g := (mgf S).symm
      _ = N.map g := by rw [← h]
      _ ≤ N := hgN
  · have h1 : N ≤ S'.map g := by
      calc N = (N.map f).map g := (mgf N).symm
        _ ≤ S'.map g := Submodule.map_mono (hfN.trans hNS')
    have h2 : S'.map g ≤ S := by
      calc S'.map g ≤ (S.map f).map g := Submodule.map_mono hS'S
        _ = S := mgf S
    rcases hmax _ h1 h2 (stab g hgT S' hS') with h | h
    · left
      apply le_antisymm _ hNS'
      calc S' = (S'.map g).map f := (mfg S').symm
        _ = N.map f := by rw [h]
        _ ≤ N := hfN
    · right
      calc S' = (S'.map g).map f := (mfg S').symm
        _ = S.map f := by rw [h]

theorem socleOver_stable_kInf : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N → (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, ∀ Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om v) N (GlobalTheory.ThK.PolData B G.M), om (1, k) Φ ∈ GlobalTheory.ThKLocSS.socleOver (GlobalTheory.ThKLocSS.opsAt om v) N (GlobalTheory.ThK.PolData B G.M) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' h N hN _ v k hk Φ hΦ
  have hk' := GlobalTheory.ThetaFacCompl.inv_mem_KInf B.emb hk
  set D := GlobalTheory.ThK.PolData B G.M
  set T := opsAt om v
  set f := om (1, k)
  set g := om (1, k⁻¹)
  have hfg : f * g = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, ← Prod.one_eq_mk, map_one]
  have hgf : g * f = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, inv_mul_cancel, ← Prod.one_eq_mk, map_one]
  have comm : ∀ k₀ ∈ KInf σ G.W B.emb, ∀ t ∈ T, t * om (1, k₀) = om (1, k₀) * t := by
    rintro k₀ hk₀ _ ⟨h₀, hh₀, rfl⟩
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one,
      commute_of_evI_evFin v hk₀.1 hh₀]
  have hfN : N.map f ≤ N := Submodule.map_le_iff_le_comap.2 fun x hx => hN.stab.cpt k hk x hx
  have hgN : N.map g ≤ N := Submodule.map_le_iff_le_comap.2 fun x hx => hN.stab.cpt k⁻¹ hk' x hx
  have hfD : ∀ x ∈ D, f x ∈ D := fun x hx =>
    GlobalTheory.PolCompact.polData_stable_kInf hK.base h.base h.geo.hV h.geo.hW h.geo.hM h.weil hk hx
  have hle : socleOver T N D ≤ (socleOver T N D).comap f := by
    refine sup_le (fun x hx => le_socleOver T N D (hfN ⟨x, hx, rfl⟩)) (sSup_le ?_)
    rintro S ⟨hSD, hS⟩
    refine Submodule.map_le_iff_le_comap.1 (le_socleOver_of_simple T ?_ ?_)
    · rintro _ ⟨x, hx, rfl⟩; exact hfD x (hSD hx)
    · exact isSimpleOver_map f g hfg hgf hfN hgN (comm k hk) (comm k⁻¹ hk') hS
  exact hle hΦ

end GlobalTheory.ThKLocSS
