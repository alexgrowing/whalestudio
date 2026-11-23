import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.ChKO

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hatL_map {a b : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {Λ' : Submodule (𝓞 E) (Fin b → E)}
    (f : (Fin a → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin b → E ⊗[F] Formalism.L2.Herm.Af F))
    (hf : ∀ x ∈ Λ, ∃ y ∈ Λ', (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (y i)) =
      f fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ, f x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, e⟩ := hf x hx
    exact Submodule.subset_span ⟨y, hy, e⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

open GlobalTheory.Doubling in

theorem pairVec_mem_hatL {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) {Λ : Submodule (𝓞 E) (Fin a → E)}
    {Λ' : Submodule (𝓞 E) (Fin b → E)} (x : Fin a → E ⊗[F] Formalism.L2.Herm.Af F) (y : Fin b → E ⊗[F] Formalism.L2.Herm.Af F) :
    pairVec e x y ∈ Formalism.L2.Herm.hatL (F := F) (sumLat e Λ Λ') ↔
      x ∈ Formalism.L2.Herm.hatL (F := F) Λ ∧ y ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · have := hatL_map (Λ := sumLat e Λ Λ') (Λ' := Λ) (LinearMap.funLeft _ _ (e ∘ .inl)) (fun x hx => ⟨_, hx.1, rfl⟩) _ h
    convert this using 1
    funext i; simp [LinearMap.funLeft_apply]
  · have := hatL_map (Λ := sumLat e Λ Λ') (Λ' := Λ') (LinearMap.funLeft _ _ (e ∘ .inr)) (fun x hx => ⟨_, hx.2, rfl⟩) _ h
    convert this using 1
    funext i; simp [LinearMap.funLeft_apply]
  · let f₁ : (Fin a → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin c → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { toFun := fun u => pairVec e u 0
        map_add' := fun u v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
        map_smul' := fun r v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp }
    let f₂ : (Fin b → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin c → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { toFun := fun u => pairVec e 0 u
        map_add' := fun u v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
        map_smul' := fun r v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp }
    have h1 := hatL_map (Λ' := sumLat e Λ Λ') f₁ (fun u hu => ⟨pairVec e u 0, (pairVec_mem_sumLat e).2 ⟨hu, zero_mem _⟩,
      funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₁]⟩) _ h.1
    have h2 := hatL_map (Λ' := sumLat e Λ Λ') f₂ (fun u hu => ⟨pairVec e 0 u, (pairVec_mem_sumLat e).2 ⟨zero_mem _, hu⟩,
      funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₂]⟩) _ h.2
    convert add_mem h1 h2 using 1
    funext j
    obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₁, f₂]

open GlobalTheory.Doubling in

theorem isFrame_blkGL {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) {Λ : Submodule (𝓞 E) (Fin a → E)}
    {Λ' : Submodule (𝓞 E) (Fin b → E)} {β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)} {β' : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ') : IsFrame (blkGL e (β, β')) (sumLat e Λ Λ') := by
  intro x
  rw [← pairVec_eta e x, pairVec_mem_hatL, h, h']
  change _ ↔ ∀ i, (blkMat e (β⁻¹).val (β'⁻¹).val *ᵥ _) i ∈ _
  rw [blkMat_mulVec]
  refine ⟨fun H j => ?_, fun H => ⟨fun i => ?_, fun i => ?_⟩⟩
  · obtain ⟨i | i, rfl⟩ := e.surjective j
    · rw [pairVec_inl]; exact H.1 i
    · rw [pairVec_inr]; exact H.2 i
  · have := H (e (.inl i)); rwa [pairVec_inl] at this
  · have := H (e (.inr i)); rwa [pairVec_inr] at this

theorem isFrame_neg {a : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) : IsFrame (-β) Λ := by
  intro x
  rw [h, inv_neg, Units.val_neg, neg_mulVec]
  exact forall_congr' fun i => neg_mem_iff.symm

theorem int_change {a : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {β β' : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (i j : Fin a) : (β'⁻¹ * β).val i j ∈ Formalism.L2.Herm.intAf F E := by
  have h1 := (h (β.val *ᵥ Pi.single j 1)).2 fun l => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 := (h' _).1 h1 i
  rwa [mulVec_mulVec, mulVec_single_one] at h2

end Lat

variable {D : D7}

theorem isEquiv_val (w : Pl D.host.E) :
    (ValuativeRel.valuation (Kw w)).IsEquiv (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem change_mem_KO {a : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {β β' : GL (Fin a) (Formalism.IndefR.Lev.EAf D)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (w : Pl D.host.E) : (loc w β')⁻¹ * loc w β ∈ KO (Kw w) (Fin a) := by
  have key : ∀ {β β' : GL (Fin a) (Formalism.IndefR.Lev.EAf D)}, IsFrame β Λ → IsFrame β' Λ → ∀ i j,
      ((loc w β')⁻¹ * loc w β).val i j ∈ (ValuativeRel.valuation (Kw w)).integer := fun {β β'} h h' i j => by
    have h2 := (mem_OA_iff _).1 (int_change h h' i j) w
    rw [← map_inv, ← map_mul]
    exact (isEquiv_val w).le_one_iff_le_one.2 h2
  refine (mem_KO_iff _).2 ⟨key h h', ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  exact key h' h

theorem reGL_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) {g : GL a k} (hg : g ∈ KO k a) :
    GlobalTheory.StepData.reGL e g ∈ KO k b := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hg
  refine (mem_KO_iff _).2 ⟨fun i j => h1 _ _, fun i j => ?_⟩
  rw [← map_inv]
  exact h2 _ _

theorem scalar_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a : Type} [Fintype a] [DecidableEq a] (u : kˣ) (hu : ValuativeRel.valuation k u = 1) :
    Units.map (Matrix.scalar a).toMonoidHom u ∈ KO k a := by
  have key : ∀ u : kˣ, ValuativeRel.valuation k u = 1 → ∀ i j,
      (Units.map (Matrix.scalar a).toMonoidHom u).val i j ∈ (ValuativeRel.valuation k).integer := fun u hu i j => by
    change Matrix.diagonal (fun _ => (u : k)) i j ∈ _
    rw [diagonal_apply]
    split_ifs
    exacts [hu.le, zero_mem _]
  refine (mem_KO_iff _).2 ⟨key u hu, ?_⟩
  rw [← map_inv]
  exact key _ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])

theorem val_xiAt (w : Pl D.host.E)
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    ValuativeRel.valuation (Kw w) (xiAt w) = 1 := by
  have hn : ∀ n : ℕ, n ∣ D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK → w.valuation D.host.E (n : D.host.E) = 1 := by
    rintro n ⟨m, hm⟩
    have : (n : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hw (by rw [hm, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
    have := (w.valuation_eq_one_iff_notMem (K := D.host.E)).2 this
    rwa [map_natCast] at this
  have h1 := hn _ (dvd_mul_left _ _)
  have h2 := hn D.host.d (Dvd.dvd.mul_right (dvd_mul_left _ _) _)
  have h3 : w.valuation D.host.E D.host.sqrtMinusD = 1 := by
    have := congrArg (w.valuation D.host.E) D.host.sqrtMinusD_sq
    rw [map_pow, Valuation.map_neg, h2] at this
    exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 this
  have h4 : w.valuation D.host.E D.host.xi0 = 1 := by
    unfold Formalism.BasicNotions.Host.xi0
    rw [map_div₀, map_mul, h1, h3, Valuation.map_neg, map_one, mul_one, div_one]
  refine (isEquiv_val w).eq_one_iff_eq_one.2 ?_
  exact (w.valuedAdicCompletion_eq_valuation' _).trans h4

theorem changes_mem_KO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j), SquareStanding G t →
      IsFrame X.rA.β (G.Λ (.grid (i + 1) (j + 1))) → IsFrame X.rA'.β (G.Λ (.grid i j)) → IsFrame X.rW.β (latX G i j) →
      ∀ w ∈ locPl G t, chA B t X w ∈ KO (Kw w) _ ∧ chB B t X w ∈ KO (Kw w) _ ∧ chX B t X w ∈ KO (Kw w) _ := by
  intro D T L sc G μ₀ hL B t i j X hS hA hA' hW w hw
  refine ⟨reGL_mem_KO _ (invT_mem_KO (change_mem_KO (B.isFrame_β hL i.2 j.2) hA w)),
    reGL_mem_KO _ (mul_mem (scalar_mem_KO _ (val_xiAt w (hS.2 w hw))) (change_mem_KO (B.isFrame_β hL i.2.le j.2.le) hA' w)),
    reGL_mem_KO _ (change_mem_KO hW (isFrame_blkGL finSumFinEquiv (B.isFrame_β hL i.2.le j.2)
      (isFrame_neg (B.isFrame_β hL i.2 j.2.le))) w)⟩

end GlobalTheory.TopFlip.ChKO

end
