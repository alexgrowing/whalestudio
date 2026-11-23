import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.CmpPutrNe
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ReductionCommutesTMor
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EpsTA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.EtDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubsingletonH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.InWmTeichmullerSubOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.AtlasOf

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris Formalism.Per6

namespace CrystallineSemistableComparison.HT

open CH PAlg B

variable {l : ℕ} [Fact l.Prime]

namespace Ex

section Fn
variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ht : TFil l)

def Lvl (N j n : ℕ) : Prop :=
  (∀ (r : ℕ) (x : H (pdS (Lc F κ false n) ((base l).cris n) r).fn j), (βMorF F κ r n).pull j x = 0 →
    (pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) N (rfl : r + N = r + N)).pull j x = 0) ∧
  ∀ y : MH (F.pt κ) n j, ∃ x, (βMorF F κ N n).pull j x = (tMor ht (F.pt κ) N n).pull j y

theorem sub_triv {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {G : C ⥤ ModuleCat.{0} R} (S : SubF G)
    (h : ∀ T, Subsingleton (G.obj T)) (j : ℕ) : Subsingleton (H S.fn j) :=
  subsingleton_H _ (fun T => ⟨fun x y => Subtype.ext ((h T).elim _ _)⟩) j

theorem pd_triv {b : Base} (L : b.Fun) {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (h : Subsingleton b.R) (r j : ℕ) :
    Subsingleton (H (pdS L c r).fn j) :=
  sub_triv _ (fun T => (show Subsingleton T.B from T.i.codomain_trivial)) j

theorem lvl_zero (N j : ℕ) : Lvl F κ ht N j 0 :=
  ⟨fun r _ _ => (pd_triv (Lc F κ false 0) ((base l).cris 0) (acr_zero (base l)) (r + N) j).elim _ _,
    fun _ => ⟨0, (sub_triv (TT (F.pt κ) N 0) (fun T => acr_zero T.1.obj) j).elim _ _⟩⟩

theorem back (n r : ℕ) (T : El (F.pt κ)) (x : (Oc F κ false n).obj ((βMor F κ false n).G.obj T))
    (hx : (βMor F κ false n).τ T x ∈ (TT (F.pt κ) r n).S T) :
    x ∈ (pdS (Lc F κ false n) ((base l).cris n) r).S ((βMor F κ false n).G.obj T) :=
  (mem_pdS (T := gObj F κ false n ((jE _).obj T))).2 (mem_TT.1 hx)

theorem lvl_pos (ε : Eps l) (u : Acris l) (hu : tA l = ε.μ * u) (N j n : ℕ)
    (h : RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε false n id slow_id).rees (gT F κ false n)) : Lvl F κ ht N j n :=
  ⟨fun r x hx => Rees.inj' (flt F κ ε false n id slow_id) (βMor F κ false n) (fun _ => Function.bijective_id)
      (fun r => TT (F.pt κ) r n) (back F κ n) h le_rfl hu r _ _ x hx,
    fun y => Rees.surj' (flt F κ ε false n id slow_id) (βMor F κ false n) (fun _ => Function.bijective_id)
      (fun r => TT (F.pt κ) r n) (pdFlt_zero _ _ id slow_id _ _) h le_rfl hu _ _ y⟩

theorem lvl_all {d : ℕ} (𝒜 : F.Atlas d) (j : ℕ) : ∃ N, ∀ n, Lvl F κ ht N j n :=
  (global_of (local_of (D.out l)) d j).imp fun N hN n => (eps_tA l).elim fun ε h => h.elim fun u hu =>
    match n with
    | 0 => lvl_zero F κ ht N j
    | n + 1 => lvl_pos F κ ht ε u hu N j (n + 1) (hN F κ ε false (n + 1) id slow_id n.succ_ne_zero (Or.inl rfl) 𝒜)

theorem eq_of {N j n : ℕ} (h : Lvl F κ ht N j n) (r : ℕ) (x x' : H (pdS (Lc F κ false n) ((base l).cris n) r).fn j)
    (e : (βMorF F κ r n).pull j x = (βMorF F κ r n).pull j x') :
    (pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) N (rfl : r + N = r + N)).pull j x =
      (pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) N (rfl : r + N = r + N)).pull j x' :=
  sub_eq_zero.1 ((map_sub _ x x').symm.trans (h.1 r (x - x') ((map_sub _ x x').trans (sub_eq_zero.2 e))))

theorem fam_ex {N j : ℕ} (h : ∀ n, Lvl F κ ht N j n) (y : ∀ n, MH (F.pt κ) n j)
    (hy : ∀ n, (MSys (F.pt κ) j).r n (y (n + 1)) = y n) :
    ∃ x : ∀ n, H (pdS (Lc F κ false n) ((base l).cris n) (N + N)).fn j,
      (∀ n, (pdOm (SH.redM F κ false n) (RingHom.id _) (red_cris _ n.le_succ) (N + N)).pull j (x (n + 1)) = x n) ∧
      ∀ n, (βMorF F κ (N + N) n).pull j (x n) = (tMor ht (F.pt κ) (N + N) n).pull j (y n) :=
  (Classical.axiomOfChoice fun n => (h n).2 (y n)).elim fun x hx =>
    ⟨fun n => (pdSh (Lc F κ false n) ((base l).cris n) (ht (base l) n) N (rfl : N + N = N + N)).pull j (x n),
      fun n => (Red.om_sh (SH.redM F κ false n) (red_cris _ n.le_succ) (ht (base l) (n + 1)) (ht (base l) n) N rfl j (x (n + 1))).trans
        (eq_of F κ ht (h n) N _ _ ((Red.β_red F κ N n j (x (n + 1))).trans
          ((congrArg ((Red.redT (F.pt κ) N n).pull j) (hx (n + 1))).trans ((Red.reduction_commutes_tMor ht (F.pt κ) N n j (y (n + 1))).trans
            ((congrArg ((tMor ht (F.pt κ) N n).pull j) (hy n)).trans (hx n).symm))))),
      fun n => Red.β_sh F κ ht N rfl n j (x n) (y n) (hx n)⟩

end Fn

end Ex

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (ht : TFil l) {e : E.EtFam l K}

theorem lvl_M {M : Model l K} (hM : M.Sm) (j : ℕ) : ∃ N, ∀ n, Ex.Lvl (schFn M.p) (okToOC l K) ht N j n :=
  (GlueB'.atlas_of hM).elim fun _ hA => Ex.lvl_all _ _ ht hA.some j

theorem exists_isLift_of_etP (he : EtP e) : ∀ M : Model l K, M.Sm → ∀ j, ∃ r, ∀ v : M.T j, ∃ x, IsLift ht e r v x := fun M hM j =>
  (lvl_M ht hM j).elim fun N hN => ⟨N + N, fun v =>
    Ex.fam_ex (schFn M.p) (okToOC l K) ht hN (fun n => e M n j (v.lev n))
      fun n => (he.good.red M n j _).trans (congrArg (e M n j) (v.2 n))⟩

theorem shS_eq_of_isLift : ∀ M : Model l K, M.Sm → ∀ j, ∃ k, ∀ (r : ℕ) (v : M.T j) (x x' : Fam M r j), IsLift ht e r v x →
    IsLift ht e r v x' → shS ht k rfl x = shS ht k rfl x' := fun M hM j =>
  (lvl_M ht hM j).imp fun N hN r v x x' hx hx' => funext fun n =>
    Ex.eq_of (schFn M.p) (okToOC l K) ht (hN n) r (x n) (x' n) ((hx.2 n).trans (hx'.2 n).symm)

end CrystallineSemistableComparison.HT
