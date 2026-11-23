import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceInvariantFormKillsVanishingSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.ProdShape

variable {D : D7}

theorem isSBHalf_sub_smul {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f g : Mx D m n → ℂ}
    (hf : IsSBHalf e Λ f) (hg : IsSBHalf e Λ g) (c : ℂ) : IsSBHalf e Λ (f - c • g) := by
  obtain ⟨f1, k, hk, f2, f3⟩ := hf
  obtain ⟨g1, l, hl, g2, g3⟩ := hg
  have hne : ∀ t, (f - c • g) t ≠ 0 → f t ≠ 0 ∨ g t ≠ 0 := fun t ht => by
    by_contra h
    push_neg at h
    exact ht (by rw [Pi.sub_apply, Pi.smul_apply, h.1, h.2, smul_zero, sub_zero])
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (hne t ht).elim (f1 t) (g1 t), k * l, mul_pos hk hl, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have e1 : f (t + (k * l) • u) = f t := by
      rw [mul_smul]; exact f2 _ (nsmul_mem hu l) (hh l u hu') t
    have e2 : g (t + (k * l) • u) = g t := by
      rw [mul_comm, mul_smul]; exact g2 _ (nsmul_mem hu k) (hh k u hu') t
    rw [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, Pi.smul_apply, e1, e2]
  · rcases hne t ht with h | h
    · rw [mul_comm, mul_smul]; exact nsmul_mem (f3 t h) l
    · rw [mul_smul]; exact nsmul_mem (g3 t h) k

theorem isHalf_add_iff {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (t : Mx D m n) :
    IsHalf e (t + x) ↔ IsHalf e t := by
  rw [GlobalTheory.SplitScalar.isHalf_iff] at hx
  rw [GlobalTheory.SplitScalar.isHalf_iff, GlobalTheory.SplitScalar.isHalf_iff, smul_add, hx, add_left_inj]

theorem isSBHalf_transl {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f : Mx D m n → ℂ}
    (hf : IsSBHalf e Λ f) {x : Mx D m n} (hx : IsHalf e x) (hx' : ∃ l : ℕ, 0 < l ∧ l • x ∈ Λ) :
    IsSBHalf e Λ fun t => f (t + x) := by
  obtain ⟨f1, k, hk, f2, f3⟩ := hf
  obtain ⟨l, hl, hlx⟩ := hx'
  have hh : ∀ (j : ℕ) (u : Mx D m n), IsHalf e u → IsHalf e (j • u) := fun j u hu => by
    rw [GlobalTheory.SplitScalar.isHalf_iff] at hu ⊢
    rw [smul_comm, hu]
  refine ⟨fun t ht => (isHalf_add_iff hx t).1 (f1 _ ht), k * l, mul_pos hk hl, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · beta_reduce
    rw [add_right_comm, mul_smul]
    exact f2 _ (nsmul_mem hu l) (hh l u hu') _
  · have h1 : (k * l) • (t + x) ∈ Λ := by rw [mul_comm, mul_smul]; exact nsmul_mem (f3 _ ht) l
    have h2 : (k * l) • x ∈ Λ := by rw [mul_smul]; exact nsmul_mem hlx k
    have := sub_mem h1 h2
    rwa [smul_add, add_sub_cancel_right] at this

theorem frMapAdj_conj_smul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (e : AE D) (x : WO S T) :
    frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := by
  have h : (((cA D e • x).map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      toEAf D e • ((x.map (toEAf D)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ := Matrix.ext fun i j => by
    change GlobalTheory.AdelicLatMove.cF D (toEAf D (cA D e * x j i)) = toEAf D e * GlobalTheory.AdelicLatMove.cF D (toEAf D (x j i))
    rw [RingHom.map_mul, RingHom.map_mul, GlobalTheory.AdelicLatMove.toEAf_cA, GlobalTheory.PlaceVec.cF_cF_toEAf]
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq, h, Matrix.mul_smul, Matrix.smul_mul]

section Red

variable {a b : ℕ} {p : Formalism.IndefR.Datum.EAf D} {M N : Matrix (Fin a) (Fin b) (Formalism.IndefR.Datum.EAf D)}

theorem isIntM_add_iff (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hM : p • M = 0) (hN : p • N = N) :
    IsIntM (M + N) ↔ IsIntM M ∧ IsIntM N := by
  refine ⟨fun h => ?_, fun h i j => add_mem (h.1 i j) (h.2 i j)⟩
  have h1 : p • (M + N) = N := by rw [smul_add, hM, hN, zero_add]
  have h2 : IsIntM N := fun i j => by
    rw [← h1]
    exact mul_mem hp (h i j)
  exact ⟨fun i j => (add_mem_cancel_right (h2 i j)).1 (h i j), h2⟩

theorem redM_add (PP : Pl D.host.E) (hM : IsIntM M) (hN : IsIntM N) : redM PP (M + N) = redM PP M + redM PP N := by
  funext i j
  have h2 : (M + N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := add_mem (hM i j) (hN i j)
  rw [Matrix.add_apply]
  unfold redM
  rw [dif_pos h2, dif_pos (hM i j), dif_pos (hN i j), ← RingHom.map_add]
  rfl

theorem redM_smul (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hM : IsIntM M) :
    redM PP (p • M) = resS D.host.F PP ⟨p, hp⟩ • redM PP M := by
  funext i j
  have h2 : (p • M) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem hp (hM i j)
  rw [Matrix.smul_apply, smul_eq_mul]
  unfold redM
  rw [dif_pos h2, dif_pos (hM i j), ← RingHom.map_mul]
  rfl

theorem redM_add_of_one (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1 : resS D.host.F PP ⟨p, hp⟩ = 1) (hM : p • M = 0) (hN : p • N = N) (iM : IsIntM M) (iN : IsIntM N) :
    redM PP (M + N) = redM PP N := by
  have h := redM_smul PP hp ((isIntM_add_iff hp hM hN).2 ⟨iM, iN⟩)
  rw [h1, one_smul, smul_add, hM, hN, zero_add] at h
  exact h.symm

theorem redM_add_of_zero (PP : Pl D.host.E) (hp : p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h0 : resS D.host.F PP ⟨p, hp⟩ = 0) (hN : p • N = N) (iM : IsIntM M) (iN : IsIntM N) :
    redM PP (M + N) = redM PP M := by
  have h := redM_smul PP hp iN
  rw [h0, zero_smul, hN] at h
  rw [redM_add PP iM iN, h, add_zero]

end Red

theorem hasShape_adjDat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (P : Finset (Pl D.host.E)) (e e₀ : AE D) (PP : Pl D.host.E), IsIdemSum e P → PP ∈ P → Formalism.L2.NTheta.IsIdemAt e₀ PP → ∀ ω₁ ω₂ : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ, (∀ y y', y PP = y' PP → ω₁ y = ω₁ y') → (∀ y y', (∀ PP' ∈ P, PP' ≠ PP → y PP' = y' PP') → ω₂ y = ω₂ y') → ∀ f₀ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latH S T ΛS ΛT) 1 f₀ (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) f → HasShape ψ S T (cA D e₀) (adjDat S T βS βT e₀ ω₁) f := by
  intro D ψ S T hψ ΛS ΛT hS hT βS βT P e e₀ PP he hPP he₀ ω₁ ω₂ h₁ h₂ f₀ f hf₀ hf ℓ hℓ
  classical
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hfT : f = Tm (adjDat S T βS βT e fun y => ω₁ y * ω₂ y) := hall Tm hTm
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hee : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, GlobalTheory.PlaceVec.idemSum_mul_self he]
  have hec : cA D e * cA D (cA D e) = 0 := by rw [← RingHom.map_mul, he.2, RingHom.map_zero]
  have hee₀ : cA D e * cA D e₀ = cA D e₀ := by rw [← RingHom.map_mul, GlobalTheory.DiagLiftFix.idemSum_mul he hPP he₀]
  have hSB : ∀ ω : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ,
      (∀ y y', (∀ PP ∈ P, y PP = y' PP) → ω y = ω y') →
      IsSBHalf (cA D e) (latH S T ΛS ΛT) (adjDat S T βS βT e ω) := fun ω hω =>
    GlobalTheory.PlaceVec.isSBHalf_of_red hS.1 hT.1 hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
      (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) P ω hω
  have s12 := hSB (fun y => ω₁ y * ω₂ y) fun y y' h => by
    rw [h₁ y y' (h PP hPP), h₂ y y' fun Q hQ _ => h Q hQ]
  have s2 := hSB ω₂ fun y y' h => h₂ y y' fun Q hQ _ => h Q hQ
  refine ⟨ℓ (Tm (adjDat S T βS βT e ω₂)), fun x hx => ?_⟩
  have hxs : cA D e₀ • x = x := (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx
  have hx' : IsHalf (cA D e) x := by
    rw [GlobalTheory.SplitScalar.isHalf_iff, ← hxs, smul_smul, hee₀]
  have st := isSBHalf_transl s12 hx' (GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS.1 hT.1 x
    (GlobalTheory.PlaceVec.half_infPart hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx')))
  obtain ⟨hp, hp1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e₀ PP he₀
  have hN : toEAf D e₀ • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
    rw [← frMapAdj_conj_smul, hxs]
  have key := GlobalTheory.T.placeInvariantForm_kills_vanishing_schwartzBruhat D ψ S T hψ ΛS ΛT hS hT (cA D e₀) (cA D e) (GlobalTheory.SplitScalar.isSplitIdem_conj he₀.1)
    hee hec hinf hee₀ f₀ Tm hf₀ hTm ℓ hℓ _ (isSBHalf_sub_smul st s2 (adjDat S T βS βT e₀ ω₁ x)) fun t ht => by
      have hz : frMapAdj S T βS βT 0 = 0 :=
        (AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_zero
      have hM : toEAf D e₀ • frMapAdj S T βS βT t = 0 := by
        rw [← frMapAdj_conj_smul, ht, hz]
      have hI := isIntM_add_iff hp hM hN
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      unfold adjDat
      rw [GlobalTheory.PlaceVec.frMapAdj_add]
      by_cases c1 : IsIntM (frMapAdj S T βS βT x)
      · by_cases c2 : IsHalf (cA D e) t ∧ IsIntM (frMapAdj S T βS βT t)
        · rw [if_pos ⟨(isHalf_add_iff hx' t).2 c2.1, hI.2 ⟨c2.2, c1⟩⟩, if_pos ⟨hx, c1⟩, if_pos c2]
          beta_reduce
          rw [h₁ _ (fun Q => redM Q (frMapAdj S T βS βT x)) (redM_add_of_one PP hp hp1 hM hN c2.2 c1),
            h₂ _ (fun Q => redM Q (frMapAdj S T βS βT t)) fun Q _ hQ =>
              redM_add_of_zero Q hp (GlobalTheory.TameProd.resS_idem_eq_zero he₀ hQ.symm hp) hN c2.2 c1]
        · rw [if_neg c2, if_neg fun h => c2 ⟨(isHalf_add_iff hx' t).1 h.1, (hI.1 h.2).1⟩, mul_zero]
      · rw [if_neg fun h => c1 (hI.1 h.2).2, if_neg fun h => c1 h.2, zero_mul]
  rw [map_sub, map_smul, hTm.trans _ s12 x hx', ← hfT, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at key
  rw [key, mul_comm]

end GlobalTheory.DownLift.ProdShape

end
