import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

noncomputable section

namespace GlobalTheory.Cut.Check

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Mat
variable {O : Type} [CommRing O] [IsDomain O] {k : ℕ}

theorem matKO_mk (A : Matrix (Fin k) (Fin k) O) (v : Fin k → FractionRing O) :
    matKO A (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((A.map (algebraMap O (FractionRing O))).mulVec v) := rfl

theorem matKO_mul (A B : Matrix (Fin k) (Fin k) O) (x : KOG O k) :
    matKO (A * B) x = matKO A (matKO B x) := by
  induction x using Submodule.Quotient.induction_on with
  | H v => rw [matKO_mk, matKO_mk, matKO_mk, Matrix.mulVec_mulVec, Matrix.map_mul]

theorem matKO_smul_one (a : O) (x : KOG O k) :
    matKO (a • (1 : Matrix (Fin k) (Fin k) O)) x = a • x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [matKO_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    funext j
    have : ∀ x, (a • (1 : Matrix (Fin k) (Fin k) O)) j x = if j = x then a else 0 := fun x => by
      simp [Matrix.one_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, this, Pi.smul_apply]
    simp [apply_ite, Algebra.smul_def]

theorem WKG_eq_matKO {Γ : Type} [Group Γ] (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) :
    WKG M g x = matKO (M g) x := by
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl
end Mat

variable {D : D7} (i : D.nd.Loc)

theorem mem_ccOff_of {Xs : Set (D.nd.X i)} {π : D.nd.X i} {f : D.nd.X i → D.nd.O i} (hf : f ∈ D.nd.T i)
    (h : ∀ x ∈ Xs, x ∉ D.nd.Z i → f x = 0) : f π ∈ ccOff i Xs π :=
  Ideal.subset_span ⟨f, hf, h, rfl⟩

theorem ccOff_univ (π : D.nd.X i) : ccOff i Set.univ π = ccAt (D.nd.T i) (D.nd.Z i) π := by
  apply le_antisymm
  · rw [ccOff, Ideal.span_le]
    rintro _ ⟨f, hf, h, rfl⟩
    refine Ideal.mem_map_of_mem ((Pi.evalRingHom (fun _ => D.nd.O i) π).comp (D.nd.T i).val.toRingHom)
      (x := (⟨f, hf⟩ : D.nd.T i)) ?_
    rw [ccIdeal, RingHom.mem_ker]
    funext y
    exact h y.1 trivial y.2
  · rw [ccAt, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [ccIdeal, RingHom.mem_ker] at hf
    exact mem_ccOff_of i f.2 fun x _ hx => congrFun hf ⟨x, hx⟩

theorem vccOff_univ (π : D.nd.X i) : vccOff i Set.univ π = D.nd.vcc i π := by
  rw [vccOff, ccOff_univ]; rfl

theorem ccOff_anti {Xs Xs' : Set (D.nd.X i)} (h : Xs ⊆ Xs') (π : D.nd.X i) : ccOff i Xs' π ≤ ccOff i Xs π :=
  Ideal.span_mono (by
    rintro _ ⟨f, hf, h0, rfl⟩
    exact ⟨f, hf, fun x hx => h0 x (h hx), rfl⟩)

theorem ccOff_eq_top {Xs : Set (D.nd.X i)} (h : ∀ x ∈ Xs, x ∈ D.nd.Z i) (π : D.nd.X i) : ccOff i Xs π = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact mem_ccOff_of i (f := 1) (one_mem _) fun x hx hz => absurd (h x hx) hz

theorem ccOff_ne_bot (Xs : Set (D.nd.X i)) {π : D.nd.X i} (hπ : π ∈ D.nd.Z i) : ccOff i Xs π ≠ ⊥ := by
  classical
  have key : ∀ x : D.nd.X i, ∃ f ∈ D.nd.T i, f π ≠ 0 ∧ (x ≠ π → f x = 0) := by
    intro x
    by_cases hx : x = π
    · exact ⟨1, one_mem _, one_ne_zero, fun h => absurd hx h⟩
    · obtain ⟨f, hf, hne⟩ := D.nd.T_sep i x π hx
      refine ⟨f - algebraMap _ _ (f x), sub_mem hf (Subalgebra.algebraMap_mem _ _), ?_, fun _ => ?_⟩
      · simpa [sub_eq_zero] using hne.symm
      · simp
  choose f hf h1 h2 using key
  have hm : (∏ x, f x) π ∈ ccOff i Xs π :=
    mem_ccOff_of i (prod_mem fun x _ => hf x) fun x _ hz => by
      rw [Finset.prod_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ x) (h2 x fun h => hz (h ▸ hπ))
  intro h
  rw [h, Ideal.mem_bot, Finset.prod_apply] at hm
  exact (Finset.prod_ne_zero_iff.2 fun x _ => h1 x) hm

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i) (Xs : Set (D.nd.X i))

theorem inR'_one : InR' D.nd r S 1 :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, by funext x; simp⟩

theorem inY_yg (γ : GE D.nd) : InY D.nd r S (yg D.nd r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩

theorem yg_eq (γ : GE D.nd) (x' : S.X') :
    yg D.nd r S γ x' = (rTwO D.nd i r (S.p x') γ - 1) * Eel D.nd S x' := by
  simp [yg, rTwO, twistM, sub_mul]

theorem cocW_unram {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) (hU : UnrOut i r Xs)
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) (v) (h1 : v ∉ placesOver D.host.E (D.nd.l i))
    (h2 : v ∉ D.nd.S i) (h3 : v ∉ D.nd.Q i) (γ) (hγ : γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) : c γ = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, -, h0, rfl⟩ := hc
    exact h0 _ (inY_yg i r S γ) fun x' hx => by rw [yg_eq, hU v h1 h2 h3 _ hx γ hγ]; simp
  | zero => rfl
  | add a b _ _ ha hb => simp [ha, hb]
  | smul a b _ hb => simp [hb]

theorem cocW_empty {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) :
    cocW i r S ∅ ψ = ⊥ := by
  rw [cocW, Submodule.span_eq_bot]
  rintro _ ⟨φ, -, h0, rfl⟩
  funext γ
  exact h0 _ (inY_yg i r S γ) fun x' hx => hx.elim

theorem cocW_mono {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) {Xs Xs' : Set (D.nd.X i)}
    (h : Xs ⊆ Xs') : cocW i r S Xs ψ ≤ cocW i r S Xs' ψ :=
  Submodule.span_mono (by
    rintro _ ⟨φ, h1, h0, rfl⟩
    exact ⟨φ, h1, fun y hy hz => h0 y hy fun x' hx => hz x' (h hx), rfl⟩)

theorem cocW_cocycle {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hψ : ∀ g, M g = (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • ψ fun x' => rO D.nd i r (S.p x') g)
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) (g h : GE D.nd) :
    c (g * h) = c g + WKG M g (c h) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, -, rfl⟩ := hc
    have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
      ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
    have e : yg D.nd r S (g * h) = yg D.nd r S g +
        (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
          ((fun x' => rO D.nd i r (S.p x') g) * yg D.nd r S h) := by
      funext x'
      simp only [yg, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, map_mul, mul_inv, Units.val_mul, mul_sub,
        smul_sub, Matrix.mul_smul, smul_smul, mul_assoc]
      abel
    have e2 : ∀ (a : D.nd.O i) (A : Matrix (Fin k) (Fin k) (D.nd.O i)) x, matKO (a • A) x = a • matKO A x := by
      intro a A x
      rw [← matKO_smul_one, ← matKO_mul, smul_mul_assoc, one_mul]
    simp only []
    rw [e, map_add, map_smul, h1 _ hg _ (inY_yg i r S h), WKG_eq_matKO, hψ, e2]
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb, map_add]; abel
  | smul a b _ hb => simp only [Pi.smul_apply, hb, map_smul, smul_add]

theorem cocW_quad {k : ℕ} (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) {v} (hq : QuadAt i r Xs v)
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) (γ) (hγ : γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    matKO (ψ fun x' => rO D.nd i r (S.p x') γ) (c γ) = c γ := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, h0, rfl⟩ := hc
    have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') γ :=
      ⟨1, fun _ => 1, fun _ => γ, fun _ => one_mem _, by funext x; simp⟩
    have hn : InR' D.nd r S (-1) :=
      ⟨1, fun _ => -1, fun _ => 1, fun _ => neg_mem (one_mem _), by funext x; simp⟩
    have hY : InY D.nd r S ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) :=
      ⟨2, ![fun x' => rO D.nd i r (S.p x') γ, -1], fun _ => γ,
        fun j => by fin_cases j; exacts [hg, hn], by simp [Fin.sum_univ_two, sub_eq_add_neg]⟩
    have := h0 _ hY fun x' hx => by
      have hq' := hq _ hx γ hγ
      have e : ((fun x' => rO D.nd i r (S.p x') γ) * yg D.nd r S γ - yg D.nd r S γ) x' =
          (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • (((rO D.nd i r (S.p x') γ - 1) *
            (rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i))) *
              Eel D.nd S x') := by
        simp only [yg, Pi.sub_apply, Pi.mul_apply, mul_sub, sub_mul, smul_sub, Matrix.mul_smul, Matrix.smul_mul,
          smul_smul, Units.inv_mul, one_smul, mul_assoc, one_mul, mul_one]
        abel
      rw [e, hq']; simp
    rw [map_sub, sub_eq_zero, h1 _ hg _ (inY_yg i r S γ)] at this
    exact this
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha, hb, map_add]
  | smul a b _ hb => simp only [Pi.smul_apply, hb, map_smul]

end GlobalTheory.Cut.Check

end
