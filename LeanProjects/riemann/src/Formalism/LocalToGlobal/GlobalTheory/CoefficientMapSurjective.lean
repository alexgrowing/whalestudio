import Formalism.LocalToGlobal.GlobalTheory.ColValOfTiedSOfRest
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.GlobalTheory.GL4.PColStd

noncomputable section

open NumberField Matrix IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u)

abbrev Pol0 (D : D7) : Type := MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL

def rd (F : Pol0 D) (z : (D.mem u).C.Y 0) : ℂ :=
  fnOf _ (shiftOf (lamT u 0)) 1 (MvPolynomial.map D.what₂.embLL F) (T.val0.eY z)

theorem rd_add (F F' : Pol0 D) (z : (D.mem u).C.Y 0) : rd T (F + F') z = rd T F z + rd T F' z := by
  simp only [rd, map_add, Pi.add_apply]

theorem map_smul_LL (a : D.what₂.LL) (F : Pol0 D) :
    MvPolynomial.map D.what₂.embLL (a • F) = D.what₂.embLL a • MvPolynomial.map D.what₂.embLL F := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

theorem rd_smul (a : D.what₂.LL) (F : Pol0 D) (z : (D.mem u).C.Y 0) : rd T (a • F) z = D.what₂.embLL a * rd T F z := by
  simp only [rd, map_smul_LL, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]

theorem rd_unique {F F' : Pol0 D} (h : ∀ z, rd T F z = rd T F' z) : F = F' := by
  apply MvPolynomial.map_injective _ D.what₂.embLL.injective
  apply Formalism.L2.Col.fnOf_injective _ _ 1 (fun _ => by simp) (Formalism.MainNotions.Ext.Lw.frOne _)
  funext y
  have := h (T.val0.eY.symm y)
  simpa [rd] using this

theorem exists_pol (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ∃ F ∈ Formalism.L2.DIV.VV D.what₂.LL ((D.fm u).lam 0), ∀ z, (D.fm u).emb 0 x c z = rd T F z := by
  obtain ⟨-, h⟩ := (T.val0.rat ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩
  obtain ⟨P, hP, hz⟩ := h c
  obtain ⟨F, hF, rfl⟩ := Formalism.L2.Col.exists_VV_of_mem_RatSpanG D.what₂.embLL _ hP
  exact ⟨F, hF, hz⟩

def pol (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) : Pol0 D := (exists_pol T x c).choose

theorem pol_mem (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    pol T x c ∈ Formalism.L2.DIV.VV D.what₂.LL ((D.fm u).lam 0) := (exists_pol T x c).choose_spec.1

theorem pol_spec (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) (z : (D.mem u).C.Y 0) :
    (D.fm u).emb 0 x c z = rd T (pol T x c) z := (exists_pol T x c).choose_spec.2 z

def co0 : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → Pol0 D) where
  toFun x c := pol T x c
  map_add' x y := funext fun c => rd_unique T fun z => by
    rw [Pi.add_apply, rd_add, ← pol_spec, ← pol_spec, ← pol_spec, map_add]
    rfl
  map_smul' a x := funext fun c => rd_unique T fun z => by
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [rd_smul, ← pol_spec, ← pol_spec, LinearMap.map_smulₛₗ]
    rfl

theorem coefficient_map_apply (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) : co0 T x c = pol T x c := rfl

theorem coefficient_map_injective : Function.Injective (co0 T) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply (D.fm u).emb_inj 0
  rw [map_zero]
  funext c z
  rw [pol_spec, ← coefficient_map_apply, hx]
  simp [rd]

theorem coefficient_map_mem_span (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    co0 T x c ∈ Formalism.MainNotions.flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0) := by
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.translate_span_eq]
  exact pol_mem T x c

theorem coefficient_map_surjective (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (F : (D.mem u).C.cls 0 → Pol0 D)
    (hF : ∀ c, F c ∈ Formalism.MainNotions.flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0)) : ∃ x, co0 T x = F := by
  have hF' : ∀ c, F c ∈ Formalism.L2.DIV.VV D.what₂.LL ((D.fm u).lam 0) := fun c => by
    have := hF c
    rwa [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.translate_span_eq] at this
  have hs : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))),
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        T.cls0.lev.U.map (MulAut.conj (T.cls0.y c).1).toMonoidHom → γ = 1 := by
    intro c γ hγ
    obtain ⟨s, hs⟩ := (T.cls0.stabI_range c γ).2 hγ
    have := hst c
    rw [← hs, Subsingleton.elim s 1, map_one]
  have hFi : (fun c z => rd T (F c) z) ∈ (D.fm u).Fi 0 := by
    rw [T.val0.Fi, Formalism.MainNotions.Ext.Lw.fiC_eq_pi _ _ _ _ T.cls0.y_bij hs, Submodule.mem_pi]
    intro c _
    rw [Formalism.MainNotions.Ext.Lw.valC_eq]
    refine ⟨MvPolynomial.map D.what₂.embLL (F c), ?_, ?_⟩
    · rw [lamT_zero u, ← Formalism.MainNotions.Ext.Lw.cspan_eq]
      exact Formalism.L2.Col.map_mem_CSpan D.what₂.embLL _ _ (hF' c)
    · funext y
      simp [rd]
  obtain ⟨x, hx⟩ := (T.val0.rat (fun c z => rd T (F c) z)).2
    ⟨hFi, fun c => ⟨_, Formalism.L2.Col.map_mem_RatSpanG D.what₂.embLL _ (hF' c), fun z => rfl⟩⟩
  refine ⟨x, funext fun c => rd_unique T fun z => ?_⟩
  rw [coefficient_map_apply, ← pol_spec, hx]

end Formalism.L2.GlobalTheoryTheory.ColValS
