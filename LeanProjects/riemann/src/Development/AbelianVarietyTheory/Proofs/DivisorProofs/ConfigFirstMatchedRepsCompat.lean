import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

open scoped Classical

namespace GlobalTheory.LowPartFin

open GlobalTheory.RealLift

section Ladder

variable {F : Type} [Field F] [NumberField F] {P Q R S : ℕ}

def atPlL (w : InfinitePlace F) :
    Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S) →ₗ[ℂ] Module.End ℂ (Tens F P Q R S) where
  toFun L := atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) w L
  map_add' L₁ L₂ := by simp only [atPl]; exact PiTensorProduct.map_update_add _ _ _ _
  map_smul' a L := by simp only [atPl]; exact PiTensorProduct.map_update_smul _ _ _ _

def ladder (i : InfinitePlace F × Formalism.BasicNotions.TH.Ln P Q R S × Bool) : Module.End ℂ (Tens F P Q R S) :=
  atPlL i.1 (if i.2.2 then Formalism.BasicNotions.TH.raiB i.2.1 else Formalism.BasicNotions.TH.lowB i.2.1)

variable (F P Q R S) in

def lev (k : ℕ) : Submodule ℂ (Tens F P Q R S) :=
  Nat.rec (motive := fun _ => Submodule ℂ (Tens F P Q R S))
    (Submodule.span ℂ {PiTensorProduct.tprod ℂ fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)})
    (fun _ N => N ⊔ ⨆ i, N.map (ladder i)) k

theorem lev_fd (k : ℕ) : FiniteDimensional ℂ (lev F P Q R S k) := by
  induction k with
  | zero => exact FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)
  | succ k ih =>
    show FiniteDimensional ℂ ↥(lev F P Q R S k ⊔ ⨆ i, (lev F P Q R S k).map (ladder i))
    infer_instance

theorem lev_le_succ (k : ℕ) : lev F P Q R S k ≤ lev F P Q R S (k + 1) := le_sup_left

theorem atPl_heisOp_mem (w : InfinitePlace F) (c : Matrix (Formalism.BasicNotions.TH.Ix P Q) (Formalism.BasicNotions.TH.Ix R S) ℂ) :
    atPlL w (heisOp c) ∈ Submodule.span ℂ (Set.range (ladder (F := F) (P := P) (Q := Q) (R := R) (S := S))) := by
  have h : heisOp c ∈ Submodule.span ℂ
      (Set.range fun j : Formalism.BasicNotions.TH.Ln P Q R S × Bool => if j.2 then Formalism.BasicNotions.TH.raiB j.1 else Formalism.BasicNotions.TH.lowB j.1) := by
    unfold heisOp
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun l _ => Submodule.sub_mem _ ?_ ?_)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(l, true), rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(l, false), rfl⟩)
  have h2 := Submodule.mem_map_of_mem (f := atPlL w) h
  rw [Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact ⟨(w, j), rfl⟩

theorem sumPl_heisOp_mem (c : InfinitePlace F → Matrix (Formalism.BasicNotions.TH.Ix P Q) (Formalism.BasicNotions.TH.Ix R S) ℂ) (k : ℕ)
    (T : Tens F P Q R S) (hT : T ∈ lev F P Q R S k) :
    sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) (fun w => heisOp (c w)) T ∈ lev F P Q R S (k + 1) := by
  have hspan : Submodule.span ℂ (Set.range (ladder (F := F) (P := P) (Q := Q) (R := R) (S := S))) ≤
      (lev F P Q R S (k + 1)).comap (LinearMap.applyₗ (R := ℂ) T) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show ladder i T ∈ lev F P Q R S (k + 1)
    exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hT))
  have hsum : sumPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol P Q R S) (fun w => heisOp (c w)) ∈
      Submodule.span ℂ (Set.range (ladder (F := F) (P := P) (Q := Q) (R := R) (S := S))) :=
    Submodule.sum_mem _ fun w _ => atPl_heisOp_mem w (c w)
  have := hspan hsum
  simpa using this

end Ladder

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem Jm_transpose (p q : ℕ) : (Formalism.BasicNotions.TH.Jm p q)ᵀ = Formalism.BasicNotions.TH.Jm p q := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem fockDeg_finiteDimensional {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W)
    (om' : Rep σ Γ.V' Γ.W) (h : IsTriple B Γ X om om') (k : ℕ) :
    FiniteDimensional ℂ (fockDeg Γ.M B.ψ B.emb k) := by
  obtain ⟨hb, hgeo, -, -, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hgeo.hV.sig w) (hgeo.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (hgeo.hW.sig w) (hgeo.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F Γ.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F Γ.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F Γ.V.J) (incM F Γ.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ Γ.M.co 1 Complex.I A C hb.cm hb.std fr
  have hz0 : ∀ (u : Matrix (Fin a) (Fin (a + a')) (AE F E)) (t : ℝ),
      Γ.M.co.rho B.ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  have toD : ∀ u (f f₁ : SInf F (Fin a × Fin (a + a'))),
      SD (fun t => Γ.M.co.rho B.ψ (realAd F t • u)) f f₁ → ActsD (evI F) (Γ.M.heisLine B.ψ u) f f₁ :=
    fun u f f₁ h => (GlobalTheory.RealLift.actsLaws F (Fin a × Fin (a + a')) f f₁ f₁).1 _ (hz0 u) h
  have tw : ∀ w (c : Matrix (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) (Formalism.BasicNotions.TH.Ix (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) ℂ) (e : ℂ),
      A w * (e • (Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p * c * Formalism.BasicNotions.TH.Jm (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q))) * (C w)ᵀ =
        e • (Γ.V.θ w * (A w * c * (C w)ᵀ) * (Γ.W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (Γ.W.θ w)ᵀ = Formalism.BasicNotions.TH.Jm (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hCθ w, Matrix.transpose_mul, Jm_transpose]
    calc A w * (e • (Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p * c * Formalism.BasicNotions.TH.Jm (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q))) * (C w)ᵀ
        = e • ((A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) * c *
            (Formalism.BasicNotions.TH.Jm (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hAθ w, ← h2]; simp only [Matrix.mul_assoc]
  have line : ∀ f, Γ.M.IsGauss B.ψ B.emb f → ∃ z : ℂ, f = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
    rintro f ⟨ε, hε⟩
    exact GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ Γ.M.co 1 Complex.I A C Φ hb.cm hb.std fr hΦ f ε
      (fun u u' hu hu' c hc hc' f1 f1' hf hf' =>
        hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f1 f1' (toD _ _ _ hf) (toD _ _ _ hf'))
  choose A' hA' using fun w => (hA w).2
  choose C' hC' using fun w => (hC w).2
  have key : ∀ k, fockDeg Γ.M B.ψ B.emb k ≤
      (lev F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) k).map Φ := by
    intro k
    induction k with
    | zero =>
      rw [fockDeg_zero, Submodule.span_le]
      intro f hf
      obtain ⟨z, rfl⟩ := line f hf
      exact ⟨z • PiTensorProduct.tprod ℂ (fun _ => 1), Submodule.smul_mem _ _ (Submodule.subset_span rfl),
        map_smul Φ _ _⟩
    | succ k ih =>
      rw [fockDeg_succ]
      refine sup_le (ih.trans (Submodule.map_mono (lev_le_succ k))) (Submodule.span_le.2 ?_)
      rintro f₁ ⟨u, hu, f, hf, hd⟩
      obtain ⟨T, hT, rfl⟩ := ih hf
      have hc : ∀ w, u.map (piInf (B.emb w)) =
          A w * (A' w * u.map (piInf (B.emb w)) * (C' w)ᵀ) * (C w)ᵀ := by
        intro w
        rw [show A w * (A' w * u.map (piInf (B.emb w)) * (C' w)ᵀ) * (C w)ᵀ =
            (A w * A' w) * u.map (piInf (B.emb w)) * (C w * C' w)ᵀ by
              simp only [Matrix.transpose_mul, Matrix.mul_assoc], hA' w, hC' w]
        simp
      have hsd := hΦ.2 u hu _ hc T
      have heq := (GlobalTheory.RealLift.actsLaws F _ (Φ T) f₁ _).2.2.1 _ hd (toD u _ _ hsd)
      rw [heq]
      exact ⟨_, sumPl_heisOp_mem _ k T hT, rfl⟩
  haveI := lev_fd (F := F) (P := a - Γ.p) (Q := Γ.p) (R := a + a' - (Γ.p + Γ.q)) (S := Γ.p + Γ.q) k
  exact Submodule.finiteDimensional_of_le (key k)

theorem lowPartInf_finiteDimensional : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      FiniteDimensional ℂ (lowPartInf B G.M R.p) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' R Rf om₁ om₁' R₁ Rf₁ hM _
  haveI := fockDeg_finiteDimensional B G X om om' hM.triple (lowDegInf B G.M R.p)
  unfold lowPartInf
  infer_instance

end GlobalTheory.LowPartFin

end
