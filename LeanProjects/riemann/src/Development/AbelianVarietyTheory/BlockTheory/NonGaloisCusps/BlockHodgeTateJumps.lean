import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

section Jumps

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (σ : Representation LL G V)

def IsJumpMultiset (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) : Prop :=
  FiniteDimensional LL ↥(DdRE PD σ τ) ∧ ∀ a : ℤ, multV PD σ τ a = (J.count a : ℤ)

end Jumps

def blockJumps (t : ℕ) : Multiset ℤ := (Finset.Ico (0 : ℤ) (t : ℤ)).val

theorem count_blockJumps (t : ℕ) (a : ℤ) :
    (blockJumps t).count a = if 0 ≤ a ∧ a < (t : ℤ) then 1 else 0 := by
  rw [blockJumps, Multiset.count_eq_of_nodup (Finset.Ico _ _).nodup]
  simp

example : blockJumps 3 = {0, 1, 2} := by decide

def SplitsAs {k Γ : Type} [Field k] [Group Γ] {n r t : ℕ} (M : Γ →* Matrix (Fin n) (Fin n) k)
    (P : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → Γ → k) : Prop :=
  ∃ e : (Fin n → k) ≃ₗ[k] ((Fin r → k) × (Fin t → k)), ∀ (g : Γ) (u : Fin n → k),
    e ((M g).mulVec u) = ((P g).mulVec (e u).1, fun c => χ c g * (e u).2 c)

example {k : Type} [Field k] (r t : ℕ) :
    SplitsAs (twistM (1 : kˣ →* Matrix (Fin (r + t)) (Fin (r + t)) k) (MonoidHom.id kˣ))
      (twistM (1 : kˣ →* Matrix (Fin r) (Fin r) k) (MonoidHom.id kˣ)) (fun (_ : Fin t) g => (g : k)) := by
  refine ⟨LinearEquiv.ofFinrankEq _ _ (by simp), fun g u => ?_⟩
  have h : ∀ (m : ℕ) (v : Fin m → k),
      (twistM (1 : kˣ →* Matrix (Fin m) (Fin m) k) (MonoidHom.id kˣ) g).mulVec v = (g : k) • v := by
    intro m v
    change ((g : k) • (1 : Matrix (Fin m) (Fin m) k)).mulVec v = _
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h, h, map_smul]
  rfl

section HidaSetting

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i)))

def BlockSplit (π : N.X i) : Prop :=
  SplitsAs (mapM (toK N i) (rO N i r π)) (mapM (toK N i) (rhoO N i ρ π))
    (fun (c : Fin R.t) g => toK N i ((N.chi i ((c : ℕ) + 1) g : (N.O i)ˣ) : N.O i))

def HidaSetting (π : N.X i) : Prop :=
  GoodR N i r ∧ π ∈ N.Z i ∧
    Continuous (fun g => ((ρ π g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
    BlockSplit N i r ρ π

variable {N} (L : LocTheory) (nbr : Br.NBr N)

def BlockJumpsAt (π : N.X i) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E (N.l i))
    (τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw) : Prop :=
  ∃ J : Multiset ℤ,
    IsJumpMultiset (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))) τ J ∧
    IsJumpMultiset (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (rTwO N i r π))) τ
      (J + blockJumps R.t)

theorem BlockJumpsAt.mult {π : N.X i} {w : HeightOneSpectrum (𝓞 H.E)} {hw : w ∈ placesOver H.E (N.l i)}
    {τ : Br.Kw nbr i w hw →ₐ[ℚ_[N.l i]] Br.LL nbr i w hw} (h : BlockJumpsAt i r ρ L nbr π w hw τ) (a : ℤ) :
    multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (rTwO N i r π))) τ a =
      multV (Br.PD L nbr i w hw) (matRep (Br.loc nbr i w hw (WpO N i ρ π))) τ a +
        if 0 ≤ a ∧ a < (R.t : ℤ) then 1 else 0 := by
  obtain ⟨J, h1, h2⟩ := h
  rw [h1.2, h2.2, Multiset.count_add, count_blockJumps]
  split_ifs <;> simp

end HidaSetting

def BlockJumps_at (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i),
    HidaSetting D.nd i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw),
      BlockJumpsAt i r ρ D.loc D.nbr π w hw τ

def BlockJumpsF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, BlockJumps_at (Fm.D x i)

def BlockJumpsClosed (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => BlockJumpsF Fm

theorem closed_of_all (h : ∀ D : D7, BlockJumps_at D) (𝒞 : FamClass) : BlockJumpsClosed 𝒞 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun _ _ _ _ => ⟨0, fun _ _ _ => h _⟩⟩⟩

end GlobalTheory.IndefiniteRowSideFullHecke.BlockHodgeTateJumps

end
