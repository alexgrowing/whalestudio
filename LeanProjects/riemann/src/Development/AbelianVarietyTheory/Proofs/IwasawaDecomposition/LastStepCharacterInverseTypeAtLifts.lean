import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeRowTypeTopRestrictionMulLevelCharEqOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimeRowTypeTopRestrictionMulLevelCharEqOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

theorem chr_mul_prod_top_core {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι)
    (Λ : LevFam B.fields.E B.fields.K (B.R.N B.R.m) (B.primes X).vGs)
    (hΛ : ∀ w, Λ w = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w))
    (Θ : LevQFam B.fields.E B.fields.K (B.R.N B.R.m) (I.Q a))
    (hΘ : ∀ Q, Θ Q = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
      (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q))
    (x : Λ.grp) (y : Θ.grp)
    (g g' : SBof I a → Sp B.fields.E (B.R.N B.R.m) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N B.R.m)) (z : SBof I a → B.fields.K)
    (H : ∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) B.R.m P (g P) (z P) ∧
      (g' P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N B.R.m) P.1 ∧
        (∀ h : P.1 ∈ (B.primes X).vGs, ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) P.1,
          redV P.1 (g' P v) = ((x.1 ⟨P.1, h⟩)⁻¹).1.mulVec (redV P.1 v)) ∧
        ∀ h : P.1 ∈ I.Q a, g' P = ((y.1 ⟨P.1, h⟩)⁻¹).1) ∧
      CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) :
    (((Λ.chr x * Θ.chr y : B.fields.Kˣ) : B.fields.K)) * ∏ P, z P = 1 := by
  classical
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_left.2 fun P h1 h2 => Q_notMem_of_ok hOk a P h2 h1
  have e2 : ∏ P, z P = (∏ w : (B.primes X).vGs, z ⟨w.1, Finset.mem_union_left _ w.2⟩) *
      ∏ Q : I.Q a, z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
    rw [← Fintype.prod_equiv (Equiv.Finset.union _ _ hd) _ _ (fun _ => rfl), Fintype.prod_sum_type]
    rfl
  rw [e2, LevFam.chr_apply, levQ_chr_apply, Units.val_mul, Units.coe_prod, Units.coe_prod]
  have hG : ∀ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨w.1, Finset.mem_union_left _ w.2⟩ = 1 := by
    intro w
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨hg'G, hred, -⟩, hc⟩ := H ⟨w.1, Finset.mem_union_left _ w.2⟩
    have key : ∀ (l : Lev (𝓞 B.fields.E ⧸ w.1.asIdeal) B.fields.K (B.R.N B.R.m)),
        l = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w) → ∀ A (hA : A ∈ l.H),
        ∃ h0, ∃ hh0 : h0 ∈ (rowTyG I.Ch (rPsymF I.Ch) w).H, A = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 ∧
          l.lam ⟨A, hA⟩ = (rowTyG I.Ch (rPsymF I.Ch) w).lam ⟨h0, hh0⟩ := by
      intro l hl A hA
      subst hl
      obtain ⟨h0, hh0, rfl⟩ := hA
      exact ⟨h0, hh0, rfl, levDiag_lam _ _ rfl _ hh0⟩
    obtain ⟨h0, hh0, eA, elam⟩ := key _ (hΛ w) _ (x.2 w (Set.mem_univ w))
    rw [elam]
    have hmem : g'' ∈ LocE.JGsym w.1 (qOf w.1) B.R.k B.R.rS B.R.r B.R.t (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_pos w.2, hOk.sharp a, if_pos rfl] at h1
    have hz' : z ⟨w.1, Finset.mem_union_left _ w.2⟩ = LocE.lamGBS (qOf w.1) (psi0P I.Ch w.1) (chiP I.Ch w.1)
        B.R.k B.R.r B.R.t B.R.m (B.R.N B.R.m - 1) 0 g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_pos w.2, hOk.sharp a, if_pos rfl]
    have eA' : x.1 ⟨w.1, w.2⟩ = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 := eA
    have hred' : ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) w.1, redV w.1 (g' ⟨w.1, Finset.mem_union_left _ w.2⟩ v) =
        ((diagEmb (𝓞 B.fields.E ⧸ w.1.asIdeal) (Nat.sub_le (B.R.N B.R.m) 1) h0)⁻¹ : GL (Fin (B.R.N B.R.m)) _).1.mulVec (redV w.1 v) := by
      intro v hv
      rw [hred w.2 v hv, eA']
    have hc' : CongE w.1 1 (g ⟨w.1, Finset.mem_union_left _ w.2⟩) (g' ⟨w.1, Finset.mem_union_left _ w.2⟩) := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rwa [if_pos w.2] at h1
    rw [mul_comm, hz']
    exact GlobalTheory.T.typePrime_rowType_topRestriction_mul_levelChar_eq_one I.Ch w h0 hh0 _ _ g'' hmem hpr hg'G hred' hc'
  have hQ : ∀ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = 1 := by
    intro Q
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨-, -, hgy⟩, hc⟩ := H ⟨Q.1, Finset.mem_union_right _ Q.2⟩
    have hnot : Q.1 ∉ (B.primes X).vGs := Q_notMem_of_ok hOk a Q.1 Q.2
    have key : ∀ (l : LevI B.fields.E B.fields.K (B.R.N B.R.m) Q.1),
        l = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M) (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q) →
        ∀ k (hk : k ∈ l.H), ∃ hk' : k ∈ (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
          (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).H,
          l.lam ⟨k, hk⟩ = (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
            (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).lam ⟨k, hk'⟩ := by
      intro l hl k hk
      subst hl
      exact ⟨hk, rfl⟩
    obtain ⟨hk', elam⟩ := key _ (hΘ Q) _ (y.2 Q (Set.mem_univ Q))
    rw [elam]
    have hmem : g'' ∈ LocE.JQ Q.1 (qOf Q.1) B.R.r (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_neg hnot] at h1
    have hz' : z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = LocE.lamQB (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) Q.1)
        B.R.r (B.R.N B.R.m - 1) g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_neg hnot]
    have hc' : CongE Q.1 (2 * (I.cst a).M) (g ⟨Q.1, Finset.mem_union_right _ Q.2⟩) ((y.1 Q)⁻¹).1 := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rw [if_neg hnot, hgy Q.2] at h1
      exact h1
    rw [mul_comm, hz']
    exact GlobalTheory.T.twistPrime_rowType_topRestriction_mul_levelChar_eq_one (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q _ _ (hOk.idx_ok a).cst_ok.M_pos (y.1 Q) hk' _ g'' hmem hpr hc'
  calc _ = (∏ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
        z ⟨w.1, Finset.mem_union_left _ w.2⟩) * ∏ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
    _ = 1 := by
        rw [Finset.prod_eq_one fun w _ => hG w, Finset.prod_eq_one fun Q _ => hQ Q, one_mul]

theorem chr_mul_prod_topVal : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  subst hi
  rcases b with ⟨_ | b1, hb⟩
  swap
  · exact absurd (hb.1 rfl) (lt_irrefl _)
  exact chr_mul_prod_top_core I hOk a _ (fun w => congrFun (topLevAt_levG_m I.Ch I.sel (I.tup a) I.Ps _) w) _
    (fun Q => congrFun (topLevAt_levQ_m I.Ch I.sel (I.tup a) I.Ps _) Q) κ.2.1 κ.2.2 g g' z H

end GlobalTheory.Mem.Col2.AdT
