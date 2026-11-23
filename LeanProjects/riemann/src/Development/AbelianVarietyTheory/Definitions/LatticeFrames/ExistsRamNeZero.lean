import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OffModel

variable {D : D7} {u : D.what₂.Word} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

theorem pair_empty {n : Type} [IsEmpty n] : IsEmpty (Pair k n) :=
  ⟨fun P => P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])⟩

theorem offDat_empty (d : Dat D u) (j : ℕ) (hj : (D.sp.X j).rank = 0) [Nonempty ι] : IsEmpty (OffDat d k ι) :=
  ⟨fun o => by
    haveI : IsEmpty (Fin (D.sp.X j).rank) := by rw [hj]; infer_instance
    exact pair_empty.false (o.Q j (Classical.arbitrary ι))⟩

def HasFrames (p : SplitPt D k) : Prop :=
  ∀ (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k),
    b * b' = 1 → b' * b = 1 → ∃ β : Frame p S n, β.b = b

theorem HasFrames.nonempty {p : SplitPt D k} (h : HasFrames p) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n]
    (hn : Fintype.card n = S.rank) : Nonempty (Frame p S n) := by
  let e : n ≃ Fin S.rank := Fintype.equivFinOfCardEq hn
  obtain ⟨β, -⟩ := h S n ((1 : Matrix n n k).submatrix e.symm id) ((1 : Matrix n n k).submatrix id e.symm)
    ((Matrix.submatrix_mul_equiv (1 : Matrix n n k) 1 e.symm (Equiv.refl n) e.symm).trans (by simp))
    (by rw [Matrix.submatrix_mul_equiv (e₂ := e.symm)]; simp)
  exact ⟨β⟩

theorem offDat_nonempty (d : Dat D u) (p : ι → SplitPt D k) (hp : ∀ i, HasFrames (p i)) (I : List ι)
    (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (hX : ∀ j, 0 < (D.sp.X j).rank) (hL : d.Lz.rank = 1) :
    ∃ o : OffDat d k ι, o.p = p ∧ o.I = I ∧ o.χ = χ := by
  refine ⟨{ p := p, I := I, q := Classical.arbitrary _, χ := χ, hχ := hχ
            β := fun j i => ((hp i).nonempty _ _ (by simp)).some
            Q := fun j _ => stdPair k ⟨0, hX j⟩
            β₀ := fun j ρ h i => ((hp i).nonempty _ _ ?_).some
            L := fun _ => ⊥, M := fun _ _ _ => ⊥, cT := fun _ => 0, cG := fun _ => 0, τ := fun _ _ => 0, ζ₀ := 0
            γ := fun i => ((hp i).nonempty _ _ (by simp)).some
            γ₀ := fun n h i => ((hp i).nonempty _ _ ?_).some }, rfl, rfl, rfl⟩
  · have h1 := (d.bes j ρ h).o.rank_add
    have h2 := (d.bes j ρ h).line.1
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · have h1 := (d.oT n h).rank_add
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega

variable {d : Dat D u} {o : OffDat d k ι}

theorem symplO_kap (H : PinOff o) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (S : HSp D) (x y : WO S d.Lz) :
    symplO _ S (kap (o.τ j h) S x) (kap (o.τ j h) S y) = symplO S d.Lz x y := by
  have := GlobalTheory.LinkKappa.symplO_ofAdj (d.bes j 0 h).L d.Lz S (o.τ j h) (-1) (by simpa using (H.tau j h).1) x y
  simpa [kap] using this

theorem atT_off (H : PinOff o) {v : Pl D} (hv : o.atT v) : ¬ onS d v := by
  obtain ⟨i, rfl⟩ := hv
  exact H.off i

theorem finite_index (H : PinOff o) : Finite ι := Set.finite_univ_iff.1 (o.I.finite_toSet.subset fun i _ => H.all i)

theorem withS_iff (S : ∀ j, Col D u j →ₗ[ℂ] Col D u j) :
    ((withS d S).Supp1 ↔ d.Supp1) ∧ ((withS d S).Supp2 ↔ d.Supp2) ∧ ((withS d S).Base ↔ d.Base) :=
  ⟨Iff.rfl, Iff.rfl, ⟨fun h => ⟨h.com, h.st, h.top, h.p, h.pT, h.t, h.x, h.k, h.sBF, h.sFB⟩,
    fun h => ⟨h.com, h.st, h.top, h.p, h.pT, h.t, h.x, h.k, h.sBF, h.sFB⟩⟩⟩

theorem valS_of (R : RdT o) (S : ∀ j, Col D u j →ₗ[ℂ] Col D u j) (ε : ℕ → ι → 𝓀[k]ˣ)
    (hS : ∀ j, j ≤ D.R.m → ∀ ψ ∈ d.Ram j, ∀ y, d.rd j (S j ψ) y =
      o.I.foldr (fun i φ => sOp (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (ε j i) φ) (d.rd j ψ y))
    (hV : ∀ j σ h, ValAd o j σ h (ε j)) : (withS d S).ValS := by
  intro j σ h P₁ P₂ a ha a' ha'
  obtain ⟨C, hC, H⟩ := hV j σ h P₁ P₂ a ha a' ha'
  refine ⟨C, hC, fun ψ hψ y => ?_⟩
  have hj : j ≤ D.R.m := by omega
  have := H _ (R.ram j hj ψ hψ y)
  rw [← hS j hj ψ hψ y] at this
  exact this

theorem norm_tau (H : PinOff o) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ lam : D.host.E,
    o.τ j h *ᵥ o.ζ₀ = lam • (d.bes j 0 h).ζ ∧
    star lam * lam * (star (d.bes j 0 h).ζ ⬝ᵥ (d.bes j 0 h).L.gram *ᵥ (d.bes j 0 h).ζ) =
      -(D.host.xi0 * star D.host.xi0) * (star o.ζ₀ ⬝ᵥ d.Lz.gram *ᵥ o.ζ₀) := by
  obtain ⟨h1, lam, h2, -⟩ := H.tau j h
  refine ⟨lam, h2, ?_⟩
  have h3 : star (o.τ j h *ᵥ o.ζ₀) ⬝ᵥ (d.bes j 0 h).L.gram *ᵥ (o.τ j h *ᵥ o.ζ₀) =
      star o.ζ₀ ⬝ᵥ ((o.τ j h)ᴴ * ((d.bes j 0 h).L.gram * o.τ j h)) *ᵥ o.ζ₀ := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h4 : (o.τ j h)ᴴ * ((d.bes j 0 h).L.gram * o.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • d.Lz.gram := h1
  rw [h4, h2, Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul] at h3
  simpa [mul_assoc] using h3

theorem exists_ram_ne_zero (R : RdT o) {ψ : Col D u 0} (hψ : ψ ∈ (D.mem u).A.Mram) (h0 : ψ ≠ 0) :
    ∃ y, d.rd 0 ψ y ≠ 0 ∧ o.Ram 0 (d.rd 0 ψ y) := by
  rw [← R.zero] at hψ
  by_contra hc
  refine h0 (R.faithful 0 (Nat.zero_le _) ψ hψ fun y => by_contra fun hy => hc ⟨y, hy, R.ram 0 (Nat.zero_le _) ψ hψ y⟩)

theorem isS_unique (R : RdT o) {j : ℕ} (hj : j ≤ D.R.m) {ψ ψ' : Col D u j} (h : ψ ∈ d.Ram j) (h' : ψ' ∈ d.Ram j)
    (e : ∀ y, d.rd j ψ y = d.rd j ψ' y) : ψ = ψ' := by
  have := R.faithful j hj ((-1 : ℂ) • ψ + ψ') (add_mem (Submodule.smul_mem _ _ h) h') fun y => by
    rw [R.lin j hj _ ψ h ψ' h' y, e y]; simp
  rw [neg_one_smul, neg_add_eq_zero] at this
  exact this

end GlobalTheory.FinPl.OffModel

end
