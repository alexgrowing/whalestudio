import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentHolds
import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypFormsCl
import Formalism.LocalToGlobal.GroupLattices.FockModels.SwRowGenMonomial

open MvPolynomial Matrix Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

noncomputable section

namespace Formalism.L2.G.EvLe

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags Formalism.L2.G.RelativeIndexFlags.Core

theorem nuOf_anti_ev {m : ℕ} {lam : Fin (m + 1) → ℤ} (h : Antitone lam) : Antitone (nuOf lam) := by
  intro i j hij
  unfold nuOf
  exact Int.toNat_le_toNat (by have := h hij; omega)

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem vsp_le (v : Fin P.nV) :
    Vsp ℂ (P.lam0 v) ≤ Submodule.span ℂ {Y | ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
      (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
        Y = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s))} := by
  let T : Fin (P.n' v) → Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ) := fun s =>
    (fun f => map (Int.castRingHom ℂ) f) '' (weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s)) :
      Set (MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ))
  have hM : ∀ s F, F ∈ (if Antitone (lamAt (P.lam0 v) s) then
      dualWeyl ℂ (P.m + 1) (P.m + 1) (nuOf (lamAt (P.lam0 v) s)) else ⊥) → F ∈ Submodule.span ℂ (T s) := by
    intro s F hF
    have ha := lamAt_anti (P.lam0 v) (P.dom v) s
    rw [if_pos ha, ← Formalism.L2.G.Model.sw_weyl_eq ℂ (P.m + 1) (P.m + 1) le_rfl _ (nuOf_anti_ev ha),
      weyl_eq_span_int] at hF
    exact hF
  have hP := prodSpan (O := ℂ) (I := Fin (P.n' v)) (B := fun _ => MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℂ)
    (fun s => (blockEmb ℂ (S := Fin (P.n' v)) (k := P.m + 1) (n := P.m + 1) s).toLinearMap) T
  unfold Vsp tensorLat
  refine (Submodule.span_mono ?_).trans (hP.le.trans (Submodule.span_mono ?_))
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun s => hM s _ (hF s), rfl⟩
  · rintro _ ⟨F, hF, rfl⟩
    choose f hf hfe using fun s => (Set.mem_image _ _ _).1 (hF s)
    exact ⟨f, hf, Finset.prod_congr rfl fun s _ => by rw [← hfe s]; rfl⟩

theorem vtup_le : VtupR P ℂ ≤ Submodule.span ℂ {X | ∃ f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
    (∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
      X = ∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))} := by
  let T : ∀ v : Fin P.nV, Set (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) ℂ) := fun v =>
    {Y | ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
      (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
        Y = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s))}
  have hP := prodSpan (O := ℂ) (I := Fin P.nV)
    (B := fun v => MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) ℂ)
    (fun v => (rename (R := ℂ) (fun x : Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1)) => (⟨v, x⟩ : Var P))).toLinearMap) T
  unfold VtupR
  refine (Submodule.span_mono ?_).trans (hP.le.trans (Submodule.span_mono ?_))
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, fun v => vsp_le P v (hF v), rfl⟩
  · rintro _ ⟨F, hF, rfl⟩
    have hF' : ∀ v, ∃ f : Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ,
        (∀ s, f s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) ∧
          F v = ∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f s)) := hF
    choose f hf hfe using hF'
    exact ⟨f, hf, Finset.prod_congr rfl fun v _ => by rw [hfe v]; rfl⟩

variable {Tau : Type} [Fintype Tau] (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau)

theorem blockRowSubstitution_one (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ) :
    map (RingHom.id ℂ) (bl P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s f) = map (Int.castRingHom ℂ) f := by
  have hn : nAt P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s = 1 := by
    unfold nAt; split_ifs <;> simp
  have hi : niAt P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) v s = 1 := by
    unfold niAt; split_ifs <;> simp
  unfold bl
  rw [hn, hi, Matrix.det_one, _root_.one_zpow, one_smul, rowAct_one, MvPolynomial.map_id]

theorem gen_mem (G : Tau → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) (M : Tau → GL (Fin (P.m + 1)) ℂ)
    (lam : Tau → DomWeight (P.m + 1)) (hw : WtTie P rfl pos lam)
    (f : ∀ v, Fin (P.n' v) → MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) ℤ)
    (hf : ∀ v s, f v s ∈ weyl ℤ (P.m + 1) (P.m + 1) le_rfl (nuOf (lamAt (P.lam0 v) s))) :
    evC P rfl pos G (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ))
      (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))) ∈ ValC G lam := by
  choose ft hft hev using fun x : Σ v : Fin P.nV, Fin (P.n' v) =>
    (blk_ev P pos lam M (fun _ => 1) (RingHom.id ℂ) (fun m l _ => oddFact_pf ℤ m l) hw x).1 (f x.1 x.2) (hf x.1 x.2)
  have hX : (∏ v, rename (fun x => (⟨v, x⟩ : Var P)) (∏ s, blockEmb ℂ s (map (Int.castRingHom ℂ) (f v s)))) =
      map (RingHom.id ℂ) (gen P rfl pos (fun _ => (1 : GL (Fin (P.m + 1)) ℂ)) f) := by
    rw [map_gen]
    simp only [blockRowSubstitution_one]
  have hM : (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) = mcOf M (RingHom.id ℂ) := by
    funext τ; ext a b; rfl
  have key : evC P rfl pos G (mcOf M (RingHom.id ℂ)) (map (RingHom.id ℂ) (gen P rfl pos (fun _ => 1) f)) =
      fnOf G (shiftOf lam) (kcOf M (fun _ => 1) (RingHom.id ℂ))
        (ten fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) := by
    funext z
    refine evC_gen P pos lam M (fun _ => 1) (RingHom.id ℂ) G f (fun τ => ft (pos.symm τ)) (fun x => ?_) z
    show BlockRealisation P pos lam M (fun _ => 1) (RingHom.id ℂ) x (f x.1 x.2) (ft (pos.symm (pos x)))
    rw [pos.symm_apply_apply]
    exact hev x
  have hK : kcOf M (fun _ => 1) (RingHom.id ℂ) = fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) := by
    funext τ; ext a b; simp [kcOf]
  have hP : ten (fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) ∈ CSpan lam := by
    refine Submodule.subset_span ⟨_, fun τ => ?_, rfl⟩
    have h1 := hft (pos.symm τ)
    rw [pos.apply_symm_apply] at h1
    unfold delSq at h1 ⊢
    exact map_mem_weyl le_rfl _ _ h1
  have h0 : fnOf G (shiftOf lam) 1 (ten fun τ => map (Int.castRingHom ℂ) (ft (pos.symm τ))) ∈ ValC G lam :=
    Submodule.mem_map_of_mem hP
  have hu : ∀ τ, IsUnit ((M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det := fun τ =>
    (Matrix.isUnit_iff_isUnit_det _).1 (M τ).isUnit
  have h1 := Formalism.MainNotions.G.CmpJ.PFormsCl.foValC_tr lam (fun τ => (M τ : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)) hu h0
  rw [hX, hM, key, hK]
  convert h1 using 1
  funext z
  simp only [fnOf, Formalism.MainNotions.G.CmpJ.PFormsCl.foTr, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul]

end Gen

section Main

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem evC_le (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → GL (Fin n) ℂ) (lam : Tau → DomWeight n) (hw : WtTie P h pos lam) :
    ∀ Q ∈ VtupR P ℂ, evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ)) Q ∈ ValC G lam := by
  subst h
  intro Q hQ
  have hS := vtup_le P hQ
  clear hQ
  induction hS using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨f, hf, rfl⟩ := hX
    exact gen_mem P pos G M lam hw f hf
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem evValC_le (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (G : Tau → Matrix (Fin n) (Fin n) ℂ)
    (M : Tau → GL (Fin n) ℂ) (lam : Tau → DomWeight n) (hw : WtTie P h pos lam) :
    (VtupR P ℂ).map (evC P h pos G (fun τ => (M τ : Matrix (Fin n) (Fin n) ℂ))) ≤ ValC G lam :=
  Submodule.map_le_iff_le_comap.2 fun Q hQ => evC_le P h pos G M lam hw Q hQ

end Main

end Formalism.L2.G.EvLe
