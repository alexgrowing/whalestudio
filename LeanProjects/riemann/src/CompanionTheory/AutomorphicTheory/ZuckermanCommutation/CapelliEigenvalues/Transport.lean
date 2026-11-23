import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

open Matrix Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace CompanionTheory.CapEig

section rel

variable {n : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem foldr_rel
    {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Eop' : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E')}
    (Rel : (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E') → Prop)
    (hT : ∀ u a b f f', Rel f f' → Rel (Top Eop u a b f) (Top Eop' u a b f'))
    {f : Matrix (Fin n) (Fin n) ℂ → E} {f' : Matrix (Fin n) (Fin n) ℂ → E'} (h : Rel f f') :
    ∀ (t : ℕ) (u : Fin t → ℂ) (a b : Fin t → Fin n),
      Rel ((List.ofFn fun k => Top Eop (u k) (a k) (b k)).foldr (fun T h => T h) f)
        ((List.ofFn fun k => Top Eop' (u k) (a k) (b k)).foldr (fun T h => T h) f')
  | 0, _, _, _ => by simpa using h
  | t + 1, u, a, b => by
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons]
    exact hT _ _ _ _ _ (foldr_rel Rel hT h t (fun k => u k.succ) (fun k => a k.succ) (fun k => b k.succ))

theorem qminorOp_rel
    {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Eop' : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E') → (Matrix (Fin n) (Fin n) ℂ → E')}
    (Rel : (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E') → Prop)
    (hT : ∀ u a b f f', Rel f f' → Rel (Top Eop u a b f) (Top Eop' u a b f'))
    (φ : E →L[ℂ] E') (g : Matrix (Fin n) (Fin n) ℂ) (hg : ∀ f f', Rel f f' → φ (f g) = f' g)
    {f : Matrix (Fin n) (Fin n) ℂ → E} {f' : Matrix (Fin n) (Fin n) ℂ → E'} (h : Rel f f')
    {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminorOp Eop a b u f g) = qminorOp Eop' a b u f' g := by
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact hg _ _ (foldr_rel Rel hT h t (fun k => u - ((k : ℕ) : ℂ)) (fun k => a (σ k)) b)

end rel

section uj

variable {n : ℕ} {ε : Fin n → Bool} {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem ec_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    (Z : Matrix (Fin n) (Fin n) ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : EcV ε Z f g = EcV ε Z f' g := by
  obtain ⟨h1, h2, -, -⟩ := cpartMem n ε Z
  unfold EcV
  rw [io_rd_congr h h1 hg, io_rd_congr h h2 hg]

theorem top_smooth {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (u : ℂ) (a b : Fin n) :
    SmoothOnGV ε (Top (EabV ε) u a b f) := by
  unfold Formalism.QuantumDeterminants.Top
  by_cases hab : a = b
  · simp only [if_pos hab]
    exact io_smooth_add (io_smooth_smul u hf) (io_eab_smooth hf a b)
  · simp only [if_neg hab]
    exact io_smooth_add io_smooth_zero (io_eab_smooth hf a b)

theorem eab_clm (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : φ (EabV ε a b f g) = EabV ε a b (fun x => φ (f x)) g := by
  obtain ⟨h1, h2, -, -⟩ := cpartMem n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add, map_smul, (rdVPair n ε E E' φ f _ g hf h1 hg).2, (rdVPair n ε E E' φ f _ g hf h2 hg).2]

theorem capelli_clm (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (u : ℂ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : φ (capelli ε u f g) = capelli ε u (fun x => φ (f x)) g := by
  unfold capelli qdetOp
  refine qminorOp_rel (fun f f' => SmoothOnGV ε f ∧ ∀ x, inUJ ε x → φ (f x) = f' x) ?_ φ g
    (fun _ _ h => h.2 g hg) ⟨hf, fun _ _ => rfl⟩ id id u
  rintro u a b f f' ⟨hs, he⟩
  refine ⟨top_smooth hs u a b, fun x hx => ?_⟩
  unfold Formalism.QuantumDeterminants.Top
  rw [map_add, eab_clm φ hs a b hx, io_eab_congr he a b hx]
  congr 1
  split_ifs
  · rw [map_smul, he x hx]
  · exact map_zero φ

end uj

theorem capelli_localization : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  intro n ε E _ _ H P Q F₁ F₂ u g hQP hPQ hH hF hg
  unfold capelliH qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, ioh_qminor ε H P Q hQP hPQ hH]
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  refine qminorOp_rel (fun f f' => ∀ x, inUJ ε x → f x = f' x) ?_ (ContinuousLinearMap.id ℂ E) _
    (fun _ _ h => h _ hg') (fun x hx => hF _ (ioh_inUH ε H P Q x hPQ hH hx)) id id u
  intro u a b f f' he x hx
  unfold Formalism.QuantumDeterminants.Top
  beta_reduce
  rw [he x hx, ec_congr he _ hx]

theorem capelli_transport : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  intro n ε E _ _ H P Q F u g hQP hPQ hH hsm hg
  have hg' := ioh_inUJ ε H P Q g hPQ hH hg
  obtain ⟨x, hx⟩ := io_rep_mk hsm
  have h1 := ioh_qminor_rep (ioh_repr (ε := ε) (E := E) P Q) id id u hx _ hg'
  have h2 := io_qminor_rep id id u hx _ hg'
  have hc := (Formalism.FourierDecayAlt.P.contractions_covariant (Module.End ℂ (ioS ε E)) n (ioE ε E) P Q (io_gl ε E)
    hQP hPQ u 0 0 0 0).1
  unfold capelliH capelli qdetOp
  rw [ioh_qminor ε H P Q hQP hPQ hH, h1, h2]
  exact congrArg (fun T : Module.End ℂ (ioS ε E) => (T x).1 ⟨_, hg'⟩) hc

end CompanionTheory.CapEig

end
