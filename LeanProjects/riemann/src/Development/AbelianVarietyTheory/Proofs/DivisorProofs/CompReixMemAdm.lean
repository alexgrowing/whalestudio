import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot

noncomputable section

namespace GlobalTheory.DblBox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

def rIdx (n d : ℕ) : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃ Fin (n + n) × Fin d :=
  (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))

@[simp] theorem rIdx_inl (p : Fin n × Fin d) : rIdx n d (.inl p) = (finSumFinEquiv (.inl p.1), p.2) := rfl

@[simp] theorem rIdx_inr (p : Fin n × Fin d) : rIdx n d (.inr p) = (finSumFinEquiv (.inr p.1), p.2) := rfl

def upB {A : Type} (u : Matrix (Fin (n + n)) (Fin d) A) : Matrix (Fin n) (Fin d) A := fun i => u (finSumFinEquiv (.inl i))

def loB {A : Type} (u : Matrix (Fin (n + n)) (Fin d) A) : Matrix (Fin n) (Fin d) A := fun i => u (finSumFinEquiv (.inr i))

def reix {R κ κ' : Type} (e : κ ≃ κ') : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ' → R) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (Equiv.arrowCongr e (Equiv.refl R)).symm

theorem reix_apply {R κ κ' : Type} (e : κ ≃ κ') (φ : (κ → R) → ℂ) (x : κ' → R) : reix e φ x = φ (x ∘ e) := rfl

theorem reix_symm {R κ κ' : Type} (e : κ ≃ κ') : (reix (R := R) e).symm = reix e.symm := rfl

def bx (φ₁ φ₂ : Fn F n d) : Fn F (n + n) d := reix (rIdx n d) (boxFun φ₁ φ₂)

def cj (φ : Fn F n d) : Fn F n d := fun x => starRingEnd ℂ (φ x)

def IsBoxCo {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d))
    (cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d)) : Prop :=
  ∀ u, cb.e u = (Sum.elim (co.e (upB u)).1 (co.e (loB u)).1 ∘ (rIdx n d).symm,
    Sum.elim (co.e (upB u)).2 (-(co.e (loB u)).2) ∘ (rIdx n d).symm)

section Reindex₂

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

theorem reix_mem_schA (e : κ ≃ κ') {φ : (κ → AF F) → ℂ} (h : φ ∈ schA F κ) : reix e φ ∈ schA F κ' := by
  have := GlobalTheory.RestrSchA.mem_schA_comp_extend F e.symm e.symm.injective φ h
  convert this using 2 with y
  rw [reix_apply]
  congr 1
  funext k
  obtain ⟨k, rfl⟩ := e.symm.surjective k
  rw [e.symm.injective.extend_apply]
  simp

theorem reix_mem_schA_iff (e : κ ≃ κ') {φ : (κ → AF F) → ℂ} : reix e φ ∈ schA F κ' ↔ φ ∈ schA F κ :=
  ⟨fun h => by simpa [← reix_symm] using reix_mem_schA e.symm h, reix_mem_schA e⟩

open scoped Classical in
theorem comp_reix_mem_adm (e : κ ≃ κ') {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (h : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ (reix e).toLinearMap ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := h (fun z => g (Function.extend e.symm z 0))
    (GlobalTheory.RestrSchA.sb_comp_extend F e.symm.injective hg)
  refine ⟨T.comp (GlobalTheory.RestrSchA.restrS F e.symm.injective), fun f => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ← hT, LinearMap.comp_apply]
  congr 1
  funext y
  rw [← GlobalTheory.RestrSchA.pureA_extend F e.symm.injective]
  show pureA F f g (y ∘ e) = _
  congr 1
  funext k
  obtain ⟨k, rfl⟩ := e.symm.surjective k
  rw [e.symm.injective.extend_apply]
  simp

omit [Fintype κ] [Fintype κ'] in
theorem thetaSum_reix (e : κ ≃ κ') (φ : (κ → AF F) → ℂ) : thetaSum F (reix e φ) = thetaSum F φ :=
  (Equiv.arrowCongr e (Equiv.refl F)).symm.tsum_eq fun ξ => φ fun i => algebraMap F (AF F) (ξ i)

theorem schr_reix {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (e : κ ≃ κ') (a b : κ → R)
    (φ : (κ → R) → ℂ) : schr ψ (a ∘ e.symm, b ∘ e.symm) (reix e φ) = reix e (schr ψ (a, b) φ) := by
  funext x
  have h1 : x ⬝ᵥ (b ∘ e.symm) = (x ∘ e) ⬝ᵥ b := by
    simp only [dotProduct]; rw [← e.sum_comp]; simp
  have h2 : (a ∘ e.symm) ⬝ᵥ (b ∘ e.symm) = a ⬝ᵥ b := by
    simp only [dotProduct]; rw [← e.sum_comp]; simp
  simp only [schr, reix_apply, h1, h2]
  congr 2
  funext k
  simp

end Reindex₂

theorem bx_mem_schA {φ₁ φ₂ : Fn F n d} (h₁ : φ₁ ∈ schA F _) (h₂ : φ₂ ∈ schA F _) : bx φ₁ φ₂ ∈ schA F _ :=
  reix_mem_schA _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ h₁ φ₂ h₂)

theorem cj_mem_schA {φ : Fn F n d} (h : φ ∈ schA F _) : cj φ ∈ schA F _ := GlobalTheory.ConjSch.conj_mem_schA φ h

theorem thetaSum_bx {φ₁ φ₂ : Fn F n d} (h₁ : φ₁ ∈ schA F _) (h₂ : φ₂ ∈ schA F _) :
    thetaSum F (bx φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  rw [bx, thetaSum_reix, GlobalTheory.ThetaBox.thetaSum_boxFun F _ _ φ₁ h₁ φ₂ h₂]

theorem exists_boxCo {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (hJ : J₂ = dblGram finSumFinEquiv J)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d))
    (hd : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d), IsBoxCo co cb ∧
      ∀ x : Matrix (Fin (n + n)) (Fin d) E, ∃ y z : Fin (n + n) × Fin d → F,
        cb.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
  let S : Matrix (Fin (n + n)) (Fin d) (AE F E) ≃ₗ[AF F]
      Matrix (Fin n) (Fin d) (AE F E) × Matrix (Fin n) (Fin d) (AE F E) :=
    (LinearEquiv.funCongrLeft (AF F) (Fin d → AE F E) finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)
  let G : (Fin (n + n) × Fin d → AF F) ≃ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    (LinearEquiv.funCongrLeft (AF F) (AF F) (rIdx n d)).trans (LinearEquiv.sumArrowLequivProdArrow _ _ (AF F) _)
  let T := (LinearEquiv.prodProdProdComm (AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F) (Fin n × Fin d → AF F)
    (Fin n × Fin d → AF F)).trans ((LinearEquiv.refl (AF F) _).prodCongr
      ((LinearEquiv.refl (AF F) (Fin n × Fin d → AF F)).prodCongr (LinearEquiv.neg (AF F) (M := Fin n × Fin d → AF F))))
  let e := S.trans ((co.e.prodCongr co.e).trans (T.trans (G.symm.prodCongr G.symm)))
  have he : ∀ u, e u = (Sum.elim (co.e (upB u)).1 (co.e (loB u)).1 ∘ (rIdx n d).symm,
      Sum.elim (co.e (upB u)).2 (-(co.e (loB u)).2) ∘ (rIdx n d).symm) := fun u => by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> obtain ⟨k | k, rfl⟩ := (rIdx n d).surjective k <;>
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    · exact congrArg (fun z => z.1 k) (G.apply_symm_apply _)
    · exact congrArg (fun z => z.2 k) (G.apply_symm_apply _)
    · exact congrArg (fun z => z.1 k) (G.apply_symm_apply _)
    · exact congrArg (fun z => z.2 k) (G.apply_symm_apply _)
  have hdot : ∀ a b : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
      (a ∘ (rIdx n d).symm) ⬝ᵥ (b ∘ (rIdx n d).symm) = a ⬝ᵥ b := fun a b => by
    simp only [dotProduct]; rw [← (rIdx n d).sum_comp]; simp
  refine ⟨⟨e, fun u v => ?_⟩, he, fun x => ?_⟩
  · rw [hJ, GlobalTheory.DefDoubling.incM_dblGram, GlobalTheory.SWAniso.symp_dblGram, he, he, hdot, hdot,
      sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_neg]
    have h1 := co.form (upB u) (upB v)
    have h2 := co.form (loB u) (loB v)
    refine (congrArg₂ (· - ·) h1 h2).trans ?_
    ring
  · obtain ⟨y, z, h1⟩ := hd (upB x)
    obtain ⟨y', z', h2⟩ := hd (loB x)
    refine ⟨Sum.elim y y' ∘ (rIdx n d).symm, Sum.elim z (-z') ∘ (rIdx n d).symm, ?_⟩
    change e (incM F x) = _
    rw [he, show upB (incM F x) = incM F (upB x) from rfl, show loB (incM F x) = incM F (loB x) from rfl, h1, h2]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> obtain ⟨k | k, rfl⟩ := (rIdx n d).surjective k <;>
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, map_neg]

theorem IsBoxCo.rho_reix {J : Matrix (Fin n) (Fin n) E} {J' : Matrix (Fin d) (Fin d) E}
    {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}
    {co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')) (Fin n × Fin d)}
    {cb : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₂) (incM F J')) (Fin (n + n) × Fin d)} (h : IsBoxCo co cb)
    (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin (n + n)) (Fin d) (AE F E))
    (φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ) :
    cb.rho ψ u (reix (rIdx n d) φ) = reix (rIdx n d) (schr ψ (Sum.elim (co.e (upB u)).1 (co.e (loB u)).1,
      Sum.elim (co.e (upB u)).2 (-(co.e (loB u)).2)) φ) := by
  rw [Darboux.rho, h u, schr_reix]

end GlobalTheory.DblBox

end
