import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.WeilLocalityDbl

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a')
    (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
    (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ))
    (hW : IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd)
    (v : Pl F) (g : UG (cA σ) (dbl (incM F G.W.J))) (hg : At (evFin F v) (GlobalTheory.InertDbl.matD g - 1))
    (u : AF F) (hu : evFin F v u = 0) (p q : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F)
    (Φ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) :
      omd g (GlobalTheory.WeilM.schr B.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr B.ψ (u • p, u • q) (omd g Φ) := by

  have hw0 : dd.e.symm (u • p, u • q) = u • dd.e.symm (p, q) := by
    rw [← Prod.smul_mk, LinearEquiv.map_smul]
  have hM : u • GlobalTheory.InertDbl.matD g = u • (1 : Matrix _ _ (AE F E)) := by
    rw [← sub_eq_zero, ← smul_sub]
    exact hg u hu
  have hact : actB (cA σ) g (dd.e.symm (u • p, u • q)) = dd.e.symm (u • p, u • q) := by
    rw [hw0]
    show (u • dd.e.symm (p, q)) * (GlobalTheory.InertDbl.matD g)ᵀ = u • dd.e.symm (p, q)
    rw [Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, hM, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one]
  have h := hW.impl g (dd.e.symm (u • p, u • q)) Φ hΦ
  rw [hact] at h
  simpa only [Darboux.rho, LinearEquiv.apply_symm_apply] using h

private lemma at_add_divisor {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) {z z' : κ → AF F}
    (hz : At (evFin F v) z) (hz' : At (evFin F v) z') : At (evFin F v) (z + z') := by
  intro u hu
  rw [smul_add, hz u hu, hz' u hu, add_zero]

private lemma at_liftV' {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) (t : κ → Fv F v) :
    At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
  intro u hu
  funext i
  show u • GlobalTheory.LatVac.liftV v (t i) = 0
  exact GlobalTheory.LatVac.at_liftV v (t i) u hu

theorem locality : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ g : UG (cA σ) (dbl (incM F G.W.J)), At (evFin F v) (GlobalTheory.InertDbl.matD g - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), Acts (evFin F v) (omd g) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v dd omd hWS g hg φ hφ
  have hW := hWS.2.1

  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) v
  have hRφ := hR φ hφ

  have htr : ∀ c : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F, (∀ i, evFin F v (c i) = 0) →
      ∀ Φ ∈ schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')),
        omd g (fun x => Φ (x + c)) = fun x => omd g Φ (x + c) := by
    intro c hc Φ hΦ
    have hu : evFin F v (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) = 0 := by
      rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]
    have huc : (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • c = c := by
      funext i
      show (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • c i = c i
      rw [smul_eq_mul, sub_mul, one_mul, GlobalTheory.WeilLocalityW.liftV_one_mul, hc i, map_zero, sub_zero]
    have h := comm_off B G dd omd hW v g hg _ hu c 0 Φ hΦ
    rw [huc, smul_zero] at h
    have hs : ∀ Ψ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ,
        GlobalTheory.WeilM.schr B.ψ (c, 0) Ψ = fun x => Ψ (x + c) := by
      intro Ψ
      funext x
      simp [GlobalTheory.WeilM.schr]
    rw [hs, hs] at h
    exact h

  refine ⟨fun t => (R 0)⁻¹ * omd g (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h1 : omd g (tens (evFin F v) φ R) ∈ schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) :=
      hW.pres g _ hRφ.2
    exact (SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ h1)
  · intro r hr
    funext y

    obtain ⟨yv, hyv⟩ : ∃ yv : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F,
        yv = fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) := ⟨_, rfl⟩
    obtain ⟨y', hy'⟩ : ∃ y' : (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F, y' = y - yv := ⟨_, rfl⟩
    have hatv : At (evFin F v) yv := by rw [hyv]; exact at_liftV' v _
    have hev : ∀ i, evFin F v (yv i) = evFin F v (y i) := by
      intro i; rw [hyv]; exact GlobalTheory.LatVac.evFin_liftV v _
    have hoff : ∀ i, evFin F v (y' i) = 0 := by
      intro i; rw [hy', Pi.sub_apply, map_sub, hev, sub_self]
    have hsum : y' + yv = y := by rw [hy', sub_add_cancel]
    have hry : r y = r y' := by rw [← hsum]; exact hr.1 y' yv hatv

    have hD : R 0 • tens (evFin F v) φ r - r y' • (fun x => tens (evFin F v) φ R (x + -y')) ∈
        schA F (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) :=
      sub_mem (Submodule.smul_mem _ _ hr.2) (Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem (-y') _ hRφ.2))
    have hvan : ∀ z, At (evFin F v) z →
        (R 0 • tens (evFin F v) φ r - r y' • (fun x => tens (evFin F v) φ R (x + -y'))) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y' := by
        rw [← hsum, add_assoc]; exact hr.1 y' (yv + z) (at_add_divisor v hatv hz)
      have e2 : y + z + -y' = 0 + (yv + z) := by rw [← hsum]; abel
      have e3 : R (y + z + -y') = R 0 := by rw [e2]; exact hRφ.1 0 (yv + z) (at_add_divisor v hatv hz)
      have e4 : (fun i => evFin F v ((y + z + -y') i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp only [Pi.add_apply, Pi.neg_apply, map_add, map_neg, hoff, neg_zero, add_zero]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, tens]
      rw [e1, e3, e4]
      ring
    have hT := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v B.ψ (omd g) hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hTr.base.std)
      (fun Φ hΦ => hW.pres g Φ hΦ) (fun μ hμ Φ hΦ => hW.unit μ hμ g Φ hΦ)
      (fun u hu p q Φ hΦ => comm_off B G dd omd hW v g hg u hu p q Φ hΦ) _ hD y hvan
    have hoff' : ∀ i, evFin F v ((-y') i) = 0 := by
      intro i; rw [Pi.neg_apply, map_neg, hoff, neg_zero]
    rw [map_sub, map_smul, map_smul, htr (-y') hoff' _ hRφ.2] at hT
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hT
    have e5 : y + -y' = yv := by rw [← hsum]; abel
    rw [e5, sub_eq_zero] at hT
    show omd g (tens (evFin F v) φ r) y =
      (R 0)⁻¹ * omd g (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i))) * r y
    rw [← hyv, hry]
    calc omd g (tens (evFin F v) φ r) y = (R 0)⁻¹ * (R 0 * omd g (tens (evFin F v) φ r) y) := by
          rw [inv_mul_cancel_left₀ hR0]
      _ = _ := by rw [hT]; ring

end GlobalTheory.WeilLocalityDbl
