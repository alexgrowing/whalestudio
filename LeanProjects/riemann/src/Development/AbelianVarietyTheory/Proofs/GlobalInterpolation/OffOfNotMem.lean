import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL

noncomputable section

namespace GlobalTheory.LvT.Built.SplitPts

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem exists_ufGL {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : GL (Fin n) E)
    (h : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1) : ∃ g : UF E n, ufGL E n g = γ := by
  obtain ⟨e, rfl⟩ := (toGLm E n).surjective γ
  refine ⟨⟨e, fun x y => ?_⟩, rfl⟩
  rw [← toGLm_mulVec e x, ← toGLm_mulVec e y]
  show star ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ x) ⬝ᵥ ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

theorem sameOff_gmap {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    {N N' : Submodule (𝓞 E) (Sp E n)} (g : Sp E n ≃ₗ[E] Sp E n) (h : SameOff ST N N') :
    SameOff ST (gmap g N) (gmap g N') := fun w hw => by
  ext x
  rw [mem_localization_gmap, mem_localization_gmap, h w hw]

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

variable (sel) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (i : ℕ)

def offSetoid : Setoid (PtAt R sel mu cst u i) where
  r := SameOffPt sel mu cst u
  iseqv :=
    ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      fun h => ⟨fun w hw => (h.1 w hw).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩,
      fun h h' => ⟨fun w hw => (h.1 w hw).trans (h'.1 w hw), h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
        h.2.2.2.trans h'.2.2.2⟩⟩

theorem off_of_notMem (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (h : (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) :
    ∀ P ∈ Pr.vT u, w ≠ P ∧ w ≠ conjPrime₂ P := fun P hP => ne_of_T_notMem hPr u ⟨P, hP⟩ h

theorem ys_congr (hPr : Pr.Ok) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal)
    {N N' : Submodule (𝓞 X.E) (Sp X.E (R.N i))} (h : SameOff (Pr.vT u) N N') :
    (ysAt R sel mu cst i).ys N' = (ysAt R sel mu cst i).ys N := by
  classical
  have h1 : ∀ w : rowSG Pr sel mu, localization₂ w.1.asIdeal N' = localization₂ w.1.asIdeal N := fun w =>
    (h w.1 (off_of_notMem u hPr
      ((Finset.mem_union.1 w.2).elim (fun h => T_notMem_vGs hPr u ⟨w.1, h⟩) (hQ w.1)))).symm
  unfold ysAt
  split_ifs
  · show ybSet sel mu cst N' = ybSet sel mu cst N
    simp only [ybSet, locLat, h1]
  · rfl

theorem exists_split : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)), ∃ sp : Split (tdatAt sel mu cst L Tp u i) (Pr.T u), ∀ b p q, (sp.off b).r p q ↔ SameOffPt sel mu cst u p q := by
  intro X Pr R _ Ch sel S mu cst L G m2 u i hX hPr hs hT _ Tp
  classical
  have hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal :=
    fun w hw => notMem_QE hs mu hw (hPr.T_prime u) hT
  have hM := moveHyp_of_ok hPr u
  have hQ' : ∀ (P : Pr.vT u) (w : QE sel (mu : Chr X.F X.E X.K)), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun P w => ne_of_T_notMem hPr u P (hQ w.1 w.2)
  have hy := ysAt_off (R := R) sel mu cst hPr u hQ i
  refine ⟨{ off := fun _ => offSetoid sel mu cst u i
            off_act := ?_
            off_lat := fun _ _ _ h => h.1
            ext := ?_
            surj := ?_
            off_up := ?_
            off_dn := ?_
            off_dia := ?_
            dia_deco := ?_
            gam_surj := ?_
            T_mem := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).1
            T_nsq := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).2
            nonconj := fun P hP Q hQ => (hM ⟨P, hP⟩).st ⟨Q, hQ⟩ }, fun _ _ _ => Iff.rfl⟩
  · rintro b g p q ⟨h1, h2, h3, h4⟩
    refine ⟨sameOff_gmap g.1.1 h1, ?_, ?_, ?_⟩
    · funext w x
      show (g.2.1.1 w).1.mulVec (p.1.1.deco.1.be w (g.1.1.symm x)) = (g.2.1.1 w).1.mulVec (q.1.1.deco.1.be w (g.1.1.symm x))
      rw [h2]
    · funext w
      show g.1.1 * p.1.1.fr w * ((g.2.2.1 w)⁻¹).1 = g.1.1 * q.1.1.fr w * ((g.2.2.1 w)⁻¹).1
      rw [h3]
    · show (fun v => g.1.1 v) '' p.1.2 = (fun v => g.1.1 v) '' q.1.2
      rw [h4]
  · rintro b p q ⟨-, h2, h3, h4⟩ h
    have hN := congrArg Deco.N h
    have hf := congrArg Deco.f h
    exact PtY.ext' (Subtype.ext (Deco.ext hN hf h2)) h3 h4
  · intro b p e he h
    have hok := GlobalTheory.LvT.Pts.ok_of_agree p.1.1.deco.2 he
      fun w => h w.1 (off_of_notMem u hPr (T_notMem_vGs hPr u w))
    have hm := PtY.mv_spec p ⟨_, hok⟩ (fun w => (h w.1 (off_of_notMem u hPr (hQ w.1 w.2))).symm)
      (ys_congr sel mu cst u i hPr hQ h)
    have e1 := congrArg Subtype.val hm.1
    refine ⟨PtY.mv p ⟨_, hok⟩, ⟨?_, (congrArg Deco.be e1).symm, hm.2.1.symm, hm.2.2.symm⟩, ?_⟩
    · rw [e1]; exact h
    · have hN := congrArg Deco.N e1
      have hf := congrArg Deco.f e1
      exact Deco.ext hN hf (funext fun w => absurd w.2 (Finset.notMem_empty _))
  · intro b p P x hx hf
    have hm := mv_up (Pr.T u) p P (hM P) (T_unif hX hPr u P) (hQ' P) (hy P) hx hf
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((upN_spec p.1.1.deco.2.lat p.1.1.deco.2.uni P.1 (hM P).ne hx).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P g hg
    have e : (tdatAt sel mu cst L Tp u i).deco b p = p.1.1.deco.1.res (Finset.empty_subset _) :=
      Deco.ext rfl rfl (funext fun w => absurd w.2 (Finset.notMem_empty _))
    rw [e] at hg
    have hg' := dn_ok_of_res p.1.1.deco.2 P (hM P) (g := g) hg
    have hm := mv_dn p P (hM P) (hQ' P) (hy P) hg'
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((p.1.1.deco.2.dnN_spec P (hM P).ne).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P a
    show SameOffPt sel mu cst u p (PtY.mv p (DecoSet.dia1 P a p.1.1.deco))
    rw [PtY.mv_dia]
    exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  · intro b p P P' a hne
    show (PtY.mv p (DecoSet.dia1 P a p.1.1.deco)).1.1.deco.1.f P' = p.1.1.deco.1.f P'
    rw [PtY.mv_dia]
    funext x
    show ((Pi.mulSingle P a : DiaG X.E (Pr.vT u)) P').1 * _ = _
    rw [Pi.mulSingle_eq_of_ne hne, Units.val_one, one_mul]
  · intro b γ h
    obtain ⟨g, hg⟩ := exists_ufGL γ h
    exact ⟨(g, 1, 1), hg⟩

end GlobalTheory.LvT.Built.SplitPts
