import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefPerEqGenPer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralFdMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorDefinitePairThetaFockVacuum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Move

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem integral_ker_move (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    {K : Subgroup (GL (Fin (G.V p.small).rank) (Lev.EAf D))} (hM : M.IsAt p.small K)
    (k : GA D (G.V p.small)) (k' : GA D (G.V p.big))
    (hk : MeasurePreserving (fun g : GA D (G.V p.small) => g * k) (M.ν p.small) (M.ν p.small))
    (hk' : Measurable fun g : GA D (G.V p.small) => g * k⁻¹)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (hF : ∀ γ ∈ GQ (G.V p.small), ∀ g, F (γ * g) = F g) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (h * k') * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p (W.om p (G.toPair p k k') f) g h * F (g * k) ∂M.ν p.small := by
  rw [← setIntegral_fd_mul_right M hM k hk hk' (fun g => W.ker p f g (h * k') * F g) ?_]
  · congr 1
    funext g
    rw [ker_mul]
  · intro γ hγ g
    have e := ker_rat_left W p hp f hf γ hγ 1 (one_mem _) g (h * k')
    rw [one_mul] at e
    simp only [e, hF γ hγ g]

theorem integral_ker_left (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (γ : GA D (G.V p.big)) (hγ : γ ∈ GQ (G.V p.big)) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (γ * h) * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p f g h * F g ∂M.ν p.small := by
  congr 1
  funext g
  have e := ker_rat_left W p hp f hf 1 (one_mem _) γ hγ g h
  rw [one_mul] at e
  rw [e]

end Move

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Paths

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem pathLift_column_leftInvariant (W : G.Weil) (M : Vol G) (t : T) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ γ ∈ GQ (G.V (.top n)), ∀ h,
      liftP W M (colPath t n) (colFam t n f) φ (γ * h) = liftP W M (colPath t n) (colFam t n f) φ h
  | 0, _, _, _, _, hφ, γ, hγ, h => hφ γ hγ h
  | n + 1, hn, f, hf, φ, _, γ, hγ, h => by
    show liftA W M (.col t n) (f (Fin.last n)) _ (γ * h) = liftA W M (.col t n) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.top t n) hn _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_row_leftInvariant (W : G.Weil) (M : Vol G) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ γ ∈ GQ (G.V (.grid n D.R.m)), ∀ h,
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (γ * h) = liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F h
  | 0, _, _, _, _, hF, γ, hγ, h => hF γ hγ h
  | n + 1, hn, f, hf, F, _, γ, hγ, h => by
    show liftA W M (.right n D.R.m) (f (Fin.last n)) _ (γ * h) = liftA W M (.right n D.R.m) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.chi n D.R.m) ⟨hn, le_rfl⟩ _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_column_translate (W : G.Weil) (M : Vol G) (t : T) (κ : ∀ n : ℕ, GA D (G.V (.top n))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ j, j < n → (∃ K, M.IsAt (.top j) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.top j)) => g * κ j) (M.ν (.top j)) (M.ν (.top j)) ∧
      Measurable (fun g : GA D (G.V (.top j)) => g * (κ j)⁻¹)) →
    ∀ (f f' : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    (∀ j : Fin n, W.om (.top t j) (G.toPair (.top t j) (κ j) (κ (j + 1))) (f j) = f' j) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ h, liftP W M (colPath t n) (colFam t n f) φ (h * κ n) =
      liftP W M (colPath t n) (colFam t n f') (fun x => φ (x * κ 0)) h
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | n + 1, hn, hκ, f, f', hf, hff, φ, hφ, h => by
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) φ) (h * κ (n + 1)) =
      liftA W M (.col t n) (f' (Fin.last n))
        (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) (fun x => φ (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.top t n) hn hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_column_leftInvariant W M t n (by omega) _ (fun j => hf j.castSucc) φ hφ) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [pathLift_column_translate W M t κ n (by omega) (fun j hj => hκ j (by omega)) _ _ (fun j => hf j.castSucc)
      (fun j => hff j.castSucc) φ hφ g]
    rfl

theorem pathLift_row_translate (W : G.Weil) (M : Vol G) (κ : ∀ n : ℕ, GA D (G.V (.grid n D.R.m))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ i, i < n → (∃ K, M.IsAt (.grid i D.R.m) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.grid i D.R.m)) => g * κ i) (M.ν (.grid i D.R.m)) (M.ν (.grid i D.R.m)) ∧
      Measurable (fun g : GA D (G.V (.grid i D.R.m)) => g * (κ i)⁻¹)) →
    ∀ (f f' : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    (∀ i : Fin n, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (κ i) (κ (i + 1))) (f i) = f' i) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ h, liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (h * κ n) =
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f') (fun x => F (x * κ 0)) h
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | n + 1, hn, hκ, f, f', hf, hff, F, hF, h => by
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f i.castSucc) F)
        (h * κ (n + 1)) =
      liftA W M (.right n D.R.m) (f' (Fin.last n))
        (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f' i.castSucc) (fun x => F (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.chi n D.R.m) ⟨hn, le_rfl⟩ hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_row_leftInvariant W M n (by omega) _ (fun i => hf i.castSucc) F hF) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [pathLift_row_translate W M κ n (by omega) (fun i hi => hκ i (by omega)) _ _ (fun i => hf i.castSucc)
      (fun i => hff i.castSucc) F hF g]
    rfl

end Paths

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Coef

variable {D : D7}

theorem pairVec_mul_real {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) {k : GA D V}
    (hk : k ∈ GinfC V) (x : GA D V) :
    pairVec c (ξ ∘ₗ c.ρ k⁻¹) Ψ x = pairVec c ξ Ψ (x * k) := by
  have e : (finHom V).rangeRestrict (x * k) = (finHom V).rangeRestrict x := by
    have hk1 : (finHom V).rangeRestrict k = 1 := Subtype.ext (by simpa using MonoidHom.mem_ker.1 hk)
    rw [map_mul, hk1, mul_one]
  have h3 : c.ρ (x * k)⁻¹ = c.ρ k⁻¹ * c.ρ x⁻¹ := (congrArg c.ρ (mul_inv_rev x k)).trans (c.ρ.map_mul _ _)
  show ξ (c.ρ k⁻¹ (c.ρ x⁻¹ (Ψ ((finHom V).rangeRestrict x)))) =
    ξ (c.ρ (x * k)⁻¹ (Ψ ((finHom V).rangeRestrict (x * k))))
  exact (congrArg (fun A : Module.End ℂ c.W => ξ (A (Ψ ((finHom V).rangeRestrict x)))) h3.symm).trans
    (congrArg (fun z => ξ (c.ρ (x * k)⁻¹ (Ψ z))) e.symm)

theorem ext_cast_mul_real {X Y : LSp D} (e : X = Y) (c : CoefA Y.sp) (v : Bridge.Gf Y.sp → c.W) (η : Module.Dual ℂ c.W)
    {k : GA D X.sp} (hk : k ∈ GinfC X.sp) (g : GA D X.sp) :
    (η ∘ₗ c.ρ (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) k)⁻¹) (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g)) =
      η (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) (g * k))) := by
  subst e
  exact pairVec_mul_real c η v hk g

end Coef

section Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem formGen_mul_real (t : T) (y : (R.HX t).H) (η : Module.Dual ℂ R.cX.W) {k : GA D (ch.G.V (.grid 0 D.R.m))}
    (hk : k ∈ GinfC (ch.G.V (.grid 0 D.R.m))) (g : GA D (ch.G.V (.grid 0 D.R.m))) :
    formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) k)⁻¹) g =
      formGen ch t y η (g * k) :=
  ext_cast_mul_real (colY_m R.toLevCh) R.cX _ η hk g

end Gen

end GlobalTheory.RowReal
