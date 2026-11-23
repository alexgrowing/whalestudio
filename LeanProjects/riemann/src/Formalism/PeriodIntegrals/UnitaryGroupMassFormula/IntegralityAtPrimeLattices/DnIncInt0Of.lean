import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityAtPrimeLattices.RootOfUnityInt

noncomputable section

namespace PI.UnitaryGroupMassFormula.IAT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField Classical IsDedekindDomain Formalism.UG

variable {D : D7} {u : D.what₂.Word}

def DnLatLoc0 (T : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)),
    g ((D.fm u).te 0 v c) = 1 →
    ∀ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
      (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U),
      (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) →
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1 →
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) →
      ∀ B B' B₂ : GL (Fin (D.R.N 0)) D.host.E,
        IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B →
        IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) B' →
        IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) ((D.fm u).dn 0 v c g) : Set _) B₂ →
        ∀ τ, IntInv w
          (atInf (embT D) (B₂⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ *
            atInf (embT D) ((γ.1⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ *
            (if τ = (D.fm u).tauOf w v then atInf (embT D) (B' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ
              else atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ))

theorem tr_int (w : D.what₂.places.Pl) (T : Forms0 D u) (h : (D.mem u).C.Y 0 → ℂ)
    (g : GL (Fin (D.R.N 0)) D.host.E) (hg : g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (M : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) (hP : P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0))
    (hPe : ∀ z, h z = fnOf _ (shiftOf (lamT u 0)) M P (T.val0.eY z))
    (Kt Ki : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ) (hK : ∀ τ, Ki τ * Kt τ = 1)
    (hN : ∀ τ, IntInv w (M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ * Ki τ)) :
    ∃ Q ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0), ∀ z,
      h (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) g hg (T.val0.eY z))) =
        fnOf _ (shiftOf (lamT u 0)) Kt Q (T.val0.eY z) := by
  let N : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ * Ki τ
  have hMK : (fun τ => M τ * atInf (embT D) (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) =
      fun τ => N τ * Kt τ := by
    funext τ
    simp only [N, Matrix.mul_assoc, hK τ, Matrix.mul_one]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u 0) τ) * subP N P, ?_, fun z => ?_⟩
  · refine bwG_intSpan_allSubP D w _ N _ ?_ P hP
    intro τ f hf
    obtain ⟨N', h1, h2, h3⟩ := hN τ
    exact local_GL_stabilises_lattice D w _ _ _ _ N' h1 h2 h3 f hf
  · rw [hPe, Equiv.apply_symm_apply, PI.UnitaryGroupMassFormula.IAT.fnOf_tr, hMK, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.fnOf_mul]

private theorem embLL_smul_mem_intSpan_of_mem_intW (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (r : D.what₂.LL) (hr : r ∈ intW D.what₂.places w) {Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ}
    (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) : D.what₂.embLL r • Q ∈ Formalism.L2.Forms.IntSpan D w lam := by
  induction hQ using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r', f, hr', hf, rfl⟩ := hp
    exact AddSubgroup.subset_closure ⟨r * r', f, mul_mem hr hr', hf, by rw [smul_smul, map_mul]⟩
  | zero => simp
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem dnIncInt0_of (T : Forms0 D u) (hC : LocalLatticeBases.ChiFin0 T) (hL : DnLatLoc0 T) : DnIncInt0 T := by
  intro w hw hseen v c g hg h hh B B' hB hB'
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hg
  obtain ⟨γ, η, κ, hη, hrel, hloc, -, htr⟩ := T.down_natural_level_zero v c g hg0
  obtain ⟨⟨B₂, hB₂⟩, -⟩ := bases0 T ((D.fm u).dn 0 v c g)
  obtain ⟨P, hP, hPe⟩ := hh B₂ hB₂
  obtain ⟨Q, hQ, hQe⟩ := tr_int w T h γ.1⁻¹
    ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) _ P hP hPe
    (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ
      else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ)
    (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ
      else atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ)
    (fun τ => by split_ifs <;> exact S0.at_infinity_mul_inv (embT D) _ τ)
    (hL w hw hseen v c g hg γ η κ hη hrel hloc B B' B₂ hB hB' hB₂)
  obtain ⟨r, hr, hre⟩ := chi_inv_int T hC w κ
  refine ⟨D.what₂.embLL r • Q, embLL_smul_mem_intSpan_of_mem_intW w _ r hr hQ, fun z => ?_⟩
  rw [htr h z (T.val0.eY.symm (frameTranslate (embT D) (fun τ x => embedding_conj_compat D τ x) γ.1⁻¹
    ((UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))).inv_mem γ.2) (T.val0.eY z))) ?_,
    hQe, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul, hre]
  intro τ
  rw [Equiv.apply_symm_apply]
  show _ = _ * (_ * _)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

end PI.UnitaryGroupMassFormula.IAT

end
