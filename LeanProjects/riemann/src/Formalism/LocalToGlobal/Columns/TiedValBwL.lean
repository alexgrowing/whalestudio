import Formalism.LocalToGlobal.Columns.TiedValBwG
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

section Deco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {d : Deco E n ST SG} {a : 𝓞 E}

theorem vb_sup_le_LshKer (hd : d.Ok) (ha : SepElt ST a) (P : ST) : d.L ⊔ P.1.asIdeal • d.Lsh ≤ d.LshKer P := by
  refine sup_le (fun x hx => (hd.mem_LshKer ha P x).2 ⟨hd.L_le_Lsh hx, ((hd.mem_L x).1 hx).2 P⟩) ?_
  refine Submodule.smul_le.2 fun p hp x hx => (hd.mem_LshKer ha P _).2 ⟨Submodule.smul_mem _ p hx, ?_⟩
  rw [hd.f_smul P p x (hd.Lsh_le_at ha P hx), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]

theorem vb_exists_smul_mem_L (hd : d.Ok) (ha : SepElt ST a) (P : ST) {y : Sp E n} (hy : y ∈ d.kerAt P) :
    ∃ s : 𝓞 E, s ∉ P.1.asIdeal ∧ s • y ∈ d.L := by
  classical
  obtain ⟨hyN, hyf⟩ := (hd.mem_kerAt P y).1 hy
  choose p hp hpP using fun Q : {Q : ST // Q ≠ P} =>
    exists_mem_notMem (P := Q.1.1) (Q := P.1) (fun e => Q.2 (Subtype.ext e))
  refine ⟨∏ Q, p Q, ?_, ?_⟩
  · intro h
    obtain ⟨Q, -, hQ⟩ := (P.1.isPrime.prod_mem_iff).1 h
    exact hpP Q hQ
  · refine (hd.mem_L _).2 ⟨Submodule.smul_mem _ _ hyN, fun Q => ?_⟩
    rw [hd.f_smul Q _ y (hd.Lsh_le_at ha Q (hd.N_le_Lsh hyN))]
    by_cases hQ : Q = P
    · subst hQ
      rw [hyf, mul_zero]
    · have h1 : (∏ Q, p Q) ∈ Q.1.asIdeal := by
        rw [← Finset.mul_prod_erase Finset.univ p (Finset.mem_univ (⟨Q, hQ⟩ : {Q : ST // Q ≠ P}))]
        exact Ideal.mul_mem_right _ _ (hp ⟨Q, hQ⟩)
      rw [Ideal.Quotient.eq_zero_iff_mem.2 h1, zero_mul]

theorem vb_LshKer_le_at (hd : d.Ok) (ha : SepElt ST a) (P : ST) {x : Sp E n} (hx : x ∈ d.LshKer P) :
    ∃ s : 𝓞 E, s ∉ P.1.asIdeal ∧ s • x ∈ d.L ⊔ P.1.asIdeal • d.Lsh := by
  have h1 : x ∈ localization₂ P.1.asIdeal (d.kerAt P) := by
    rw [← hd.locP_LshKer_self ha P]
    exact le_locP _ _ hx
  obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 h1
  obtain ⟨t, ht, htx⟩ := vb_exists_smul_mem_L hd ha P hsx
  exact ⟨t * s, fun h => (P.1.isPrime.mem_or_mem h).elim ht hs, by
    rw [mul_smul]; exact Submodule.mem_sup_left htx⟩

theorem vb_sup_lattice (hd : d.Ok) (P : ST) : Submodule.IsLattice E (d.L ⊔ P.1.asIdeal • d.Lsh) :=
  lattice_between hd.L_lattice hd.Lsh_lattice le_sup_left (sup_le hd.L_le_Lsh Submodule.smul_le_right)

end Deco

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ)
  (Pl : Rows.Places X.K) (pw : Pl.Pl → HeightOneSpectrum (𝓞 X.K))
  (hval : ∀ w (x : X.K), x ≠ 0 → Pl.val w x = ((vAdd (pw w) x : ℤ) : WithTop ℤ))

include hval hPr in
open Classical in

theorem vb_mem_locP_BvLat_iff (u : Pr.Word) (j : ℕ) (lam' : X.Tau → DomWeight (R.N j))
    (hn : ∀ τ, (W.lamTrue u j τ).natW = (lam' τ).natW) (w : Pl.Pl) (hw : Pl.resChar w = Pr.T u) (hs : seenC Pr u (pw w))
    (v : {P // P ∈ Pr.vT u}) (d : ColDeco X Pr u (R.N j)) (F : VV X.K (W.lamTrue u j)) :
    haveI := hX.nonempty_Tau
    F ∈ localization₂ (pw w).asIdeal (BvLat W u j v d) ↔
      ∀ B B' : GL (Fin (R.N j)) X.E, IsLocBasis (Pr.T u) (d.1.Lsh : Set (Fin (R.N j) → X.E)) B →
        IsLocBasis (Pr.T u) ((d.1.L ⊔ v.1.asIdeal • d.1.Lsh : Submodule (𝓞 X.E) (Fin (R.N j) → X.E)) : Set (Fin (R.N j) → X.E)) B' →
        ∃ P ∈ vlIntSpan σ₀ Pl w lam', evV X.emb (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) (W.lamTrue u j) σ₀ F =
          fnOf _ (shiftOf (W.lamTrue u j))
            (fun τ => @ite _ (τ = tauOfC (pw w) v.1) (Classical.propDecidable _)
              (atInf (embAt σ₀ X.emb) ((B'⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)
              (atInf (embAt σ₀ X.emb) ((B⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)) P := by
  have := hX.nonempty_Tau
  have ha := sepElt_of_ok hPr u
  have hT : (Pr.T u : 𝓞 X.K) ∈ (pw w).asIdeal := hw ▸ vl_resChar_mem Pl pw hval w
  set τ₀ := tauOfC (pw w) v.1 with hτ₀

  have hsee : pullW τ₀ (pw w) = v.1 := by
    rcases tauOfC_spec hX hPr u (pw w) hT v with h | h
    · exact h
    · exact absurd h ((moveHyp_of_ok hPr u v).st ⟨pullW τ₀ (pw w), (seenC_iff hPr u (pw w)).1 hs τ₀⟩)
  let M : X.Tau → Submodule (𝓞 X.E) (Fin (R.N j) → X.E) := fun τ => if τ = τ₀ then d.1.L ⊔ v.1.asIdeal • d.1.Lsh else d.1.Lsh
  have hM : ∀ τ, Submodule.IsLattice X.E (M τ) := by
    intro τ
    by_cases hτ : τ = τ₀
    · simp only [M, if_pos hτ]; exact vb_sup_lattice d.2 v
    · simp only [M, if_neg hτ]; exact d.2.Lsh_lattice
  have e1 : localization₂ (pw w).asIdeal (BvLat W u j v d) =
      localization₂ (pw w).asIdeal (delK (W.lamTrue u j) fun τ => dualFr (tauLat X.emb τ (M τ))) := by
    rw [BvLat_eq_BvLatF W hX hPr u j hs v d]
    unfold BvLatF
    refine round_locP_congr_fam X.emb (W.lamTrue u j) (pw w) (fun τ => ?_) hM (fun τ => ?_)
    · by_cases hτ : τ = τ₀
      · rw [if_pos hτ]; exact d.2.LshKer_lattice ha v
      · rw [if_neg hτ]; exact d.2.Lsh_lattice
    · by_cases hτ : τ = τ₀
      · have hτ' : τ = tauOfC (pw w) v.1 := hτ
        simp only [M, if_pos hτ]
        rw [if_pos hτ']
        subst hτ
        constructor
        · intro x hx
          obtain ⟨s, hs', hsx⟩ := vb_LshKer_le_at d.2 ha v hx
          refine ⟨s, ?_, hsx⟩
          intro h
          apply hs'
          rw [← hsee]
          exact h
        · intro x hx
          exact ⟨1, by rw [map_one]; exact one_notMem (pw w), by rw [one_smul]; exact vb_sup_le_LshKer d.2 ha v hx⟩
      · have hτ' : ¬ τ = tauOfC (pw w) v.1 := hτ
        simp only [M, if_neg hτ]
        rw [if_neg hτ']
        exact ⟨fun x hx => ⟨1, by rw [map_one]; exact one_notMem (pw w), by rwa [one_smul]⟩,
          fun x hx => ⟨1, by rw [map_one]; exact one_notMem (pw w), by rwa [one_smul]⟩⟩
  rw [e1]
  have key : ∀ B B' : GL (Fin (R.N j)) X.E, IsLocBasis (Pr.T u) (d.1.Lsh : Set (Fin (R.N j) → X.E)) B →
      IsLocBasis (Pr.T u) ((d.1.L ⊔ v.1.asIdeal • d.1.Lsh : Submodule (𝓞 X.E) (Fin (R.N j) → X.E)) : Set (Fin (R.N j) → X.E)) B' →
      (F ∈ localization₂ (pw w).asIdeal (delK (W.lamTrue u j) fun τ => dualFr (tauLat X.emb τ (M τ))) ↔
        ∃ P ∈ vlIntSpan σ₀ Pl w lam', evV X.emb (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) (W.lamTrue u j) σ₀ F =
          fnOf _ (shiftOf (W.lamTrue u j))
            (fun τ => @ite _ (τ = τ₀) (Classical.propDecidable _)
              (atInf (embAt σ₀ X.emb) ((B'⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)
              (atInf (embAt σ₀ X.emb) ((B⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)) P) := by
    intro B B' hB hB'
    have h := mem_localization_iff_forall_localBasis_of_valuation Pl pw hval X.emb σ₀ w (1 : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) (W.lamTrue u j) lam' hn M hM F
      (fun τ => if τ = τ₀ then B' else B) (fun τ => by
        rw [hw]
        by_cases hτ : τ = τ₀
        · simp only [M, if_pos hτ]; exact hB'
        · simp only [M, if_neg hτ]; exact hB)
    have e2 : (fun τ => atInf (embAt σ₀ X.emb) ((((if τ = τ₀ then B' else B) : GL (Fin (R.N j)) X.E)⁻¹ : GL (Fin (R.N j)) X.E) :
        Matrix (Fin (R.N j)) (Fin (R.N j)) X.E) τ) =
        fun τ => @ite _ (τ = τ₀) (Classical.propDecidable _)
          (atInf (embAt σ₀ X.emb) ((B'⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ)
          (atInf (embAt σ₀ X.emb) ((B⁻¹ : GL (Fin (R.N j)) X.E) : Matrix _ _ X.E) τ) := by
      funext τ
      by_cases hτ : τ = τ₀
      · rw [if_pos hτ, if_pos hτ]
      · rw [if_neg hτ, if_neg hτ]
    rw [e2] at h
    exact h
  constructor
  · intro h B B' hB hB'
    exact (key B B' hB hB').1 h
  · intro h
    have : Fact (Pr.T u).Prime := ⟨hPr.T_prime u⟩
    obtain ⟨B, hB⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pr.T u) X.E d.1.Lsh d.2.Lsh_lattice.fg d.2.Lsh_lattice.span_eq_top
    obtain ⟨B', hB'⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis (Pr.T u) X.E _ (vb_sup_lattice d.2 v).fg
      (vb_sup_lattice d.2 v).span_eq_top
    exact (key B B' hB hB').2 (h B B' hB hB')

end One

end Formalism.L2.Col
