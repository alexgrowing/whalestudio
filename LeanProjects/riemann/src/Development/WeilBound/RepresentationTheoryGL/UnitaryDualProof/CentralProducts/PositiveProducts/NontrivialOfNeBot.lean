import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Pos

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dpow_sc (m : ℕ) (s : ℝ) (x : kˣ) :
    ((dpow m s (sc m x) : ℂˣ) : ℂ) = ((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) := by
  have hd : Matrix.GeneralLinearGroup.det (sc m x) = x ^ m := by
    ext; simp [sc, Matrix.GeneralLinearGroup.scalar]
  have hn : nabs k (x ^ m) = nabs k x ^ m := by simp [nabs]
  rw [dpow, detChar_apply, val_absPow_ofReal, hd, hn, ← Real.rpow_natCast_mul (nabs_pos' k x).le]

theorem tw_eig {m : ℕ} (A : GRep k m) (s : ℝ) (x : kˣ) (v : A.V) :
    (A.tw s).ρ (sc m x) v = ((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) • A.ρ (sc m x) v := by
  show ((dpow m s (sc m x) : ℂˣ) : ℂ) • A.ρ (sc m x) v = _
  rw [dpow_sc]

theorem untw {m : ℕ} (A : GRep k m) (s : ℝ) (x : kˣ) (c : ℂ) (v : A.V) (h : (A.tw s).ρ (sc m x) v = c • v) :
    A.ρ (sc m x) v = (c * ((nabs k x ^ (-((m : ℝ) * s)) : ℝ) : ℂ)) • v := by
  rw [tw_eig] at h
  calc A.ρ (sc m x) v = ((nabs k x ^ (-((m : ℝ) * s)) : ℝ) : ℂ) • ((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) •
        A.ρ (sc m x) v := by
        rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos' k x), neg_add_cancel, Real.rpow_zero,
          Complex.ofReal_one, one_smul]
    _ = _ := by rw [h, smul_smul, mul_comm]

theorem retw {m : ℕ} (A : GRep k m) (s : ℝ) (x : kˣ) (c : ℂ) (v : A.V) (h : A.ρ (sc m x) v = c • v) :
    (A.tw s).ρ (sc m x) v = (((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) * c) • v := by
  rw [tw_eig, h, smul_smul]

theorem isSmooth_tw {m : ℕ} {A : GRep k m} (h : IsSmooth A.ρ) (s : ℝ) : IsSmooth (A.tw s).ρ :=
  isSmooth_twist h (IsSmoothChar.detChar (isSmoothChar_absPow (k := k) _))

theorem lfin_tw {m : ℕ} {A : GRep k m} (h : LFin A) (s : ℝ) : LFin (A.tw s) := by
  intro a
  obtain ⟨U, hU, ha, hst⟩ := h a
  refine ⟨U, hU, ha, fun x u hu => ?_⟩
  exact U.smul_mem ((dpow m s (sc m x) : ℂˣ) : ℂ) (hst x u hu)

theorem isSmooth_derivB (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} (π : GRep k (n + j)), IsSmooth π.ρ →
    IsSmooth (derivB ψ j π).ρ
  | 0, _, _, h => h
  | j + 1, _, _, h => GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j h

theorem isAdm_cast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : IsAdmissible π.ρ) : IsAdmissible (π.cast h).ρ := by
  subst h; exact hπ

theorem irr_cast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : π.ρ.IsIrreducible) : (π.cast h).ρ.IsIrreducible := by
  subst h; exact hπ

theorem unit_cast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : IsUnitarisable π.ρ) : IsUnitarisable (π.cast h).ρ := by
  subst h; exact hπ

theorem cast_cast {a b c : ℕ} (h : a = b) (h' : b = c) (π : GRep k a) : (π.cast h).cast h' = π.cast (h.trans h') := by
  subst h; subst h'; rfl

theorem eig_cast {a b : ℕ} (h : a = b) (π : GRep k a) (x : kˣ) (c : ℂ) (v : (π.cast h).V) (hv0 : v ≠ 0)
    (hv : (π.cast h).ρ (sc b x) v = c • v) : ∃ w : π.V, w ≠ 0 ∧ π.ρ (sc a x) w = c • w := by
  subst h; exact ⟨v, hv0, hv⟩

theorem adm {n : ℕ} (π : GRep k n) (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) : IsAdmissible π.ρ :=
  PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n π.V π.ρ hs hi

theorem norm_eig_of_unit {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hu : IsUnitarisable ρ) {g : G} {c : ℂ} {v : V} (hv : v ≠ 0) (h : ρ g v = c • v) : ‖c‖ = 1 := by
  obtain ⟨B, -, hpos, hinv⟩ := hu
  have h1 := hinv g v v
  simp only [h, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at h1
  have hB : B v v ≠ 0 := fun h0 => by have := hpos v hv; rw [h0] at this; simp at this
  have h2 : c * (starRingEnd ℂ) c = 1 := by
    apply mul_right_cancel₀ hB
    linear_combination h1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 := norm_nonneg c
  nlinarith

theorem nontrivial_of_ne_bot {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (W : Subrepresentation ρ) (hW : W ≠ ⊥) : Nontrivial W.toSubmodule := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply hW
  apply Subrepresentation.ext
  rw [Submodule.eq_bot_of_subsingleton (p := W.toSubmodule)]
  rfl

theorem subquot_sub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (W : Subrepresentation ρ) : IsSubquotient W.toRepresentation ρ :=
  ⟨W, Representation.IntertwiningMap.id _, Function.surjective_id⟩

theorem pipe (hL : GlobalTheory.RgGu.Leib.LeibnizOrd k) (hLF : LFDeriv k) (hE : EigProd k) (hF : EigFilt k)
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {r t : ℕ} (π₁ : GRep k r) (π₂ : GRep k t)
    (hs₁ : IsSmooth π₁.ρ) (ha₁ : IsAdmissible π₁.ρ) (hs₂ : IsSmooth π₂.ρ) (ha₂ : IsAdmissible π₂.ρ)
    (ℓ n : ℕ) (e : r + t = n + ℓ) (x : kˣ) (c : ℂ) (v : (derivB ψ ℓ ((π₁.prod π₂).cast e)).V) (hv0 : v ≠ 0)
    (hv : (derivB ψ ℓ ((π₁.prod π₂).cast e)).ρ (sc n x) v = c • v) :
    ∃ (i : ℕ) (h : i ≤ r ∧ ℓ - i ≤ t) (cA cB : ℂ), i ≤ ℓ ∧ c = cA * cB ∧
      (∃ a : ((derivB ψ i (π₁.cast (Nat.sub_add_cancel h.1).symm)).tw (((ℓ - i : ℕ) : ℝ) / 2)).V, a ≠ 0 ∧
        ((derivB ψ i (π₁.cast (Nat.sub_add_cancel h.1).symm)).tw (((ℓ - i : ℕ) : ℝ) / 2)).ρ (sc (r - i) x) a =
          cA • a) ∧
      ∃ b : ((derivB ψ (ℓ - i) (π₂.cast (Nat.sub_add_cancel h.2).symm)).tw ((i : ℝ) / 2)).V, b ≠ 0 ∧
        ((derivB ψ (ℓ - i) (π₂.cast (Nat.sub_add_cancel h.2).symm)).tw ((i : ℝ) / 2)).ρ (sc (t - (ℓ - i)) x) b =
          cB • b := by
  obtain ⟨F, hanti, h0, hbot, hpieces⟩ := hL ψ hc h1 r t ℓ n e π₁ π₂ hs₁ hs₂
  obtain ⟨i, hi, w, hw0, hw⟩ := hF n _ (derivB ψ ℓ ((π₁.prod π₂).cast e)).ρ ℓ F hanti h0 hbot x c v hv0 hv
  have hp := hpieces i hi
  split_ifs at hp with h
  · obtain ⟨hsz, ⟨eq⟩⟩ := hp
    have hw' := GlobalTheory.CompanionTheory.LeibOrd.eint eq (sc n x) w
    rw [hw, map_smul] at hw'
    have hw0' : eq w ≠ 0 := fun h0' =>
      hw0 (eq.toLinearEquiv.injective ((show eq.toLinearEquiv w = 0 from h0').trans (map_zero _).symm))
    obtain ⟨f, hf0, hf⟩ := eig_cast hsz _ x c _ hw0' hw'.symm
    have hsA := isSmooth_tw (isSmooth_derivB ψ i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast
      (Nat.sub_add_cancel h.1).symm hs₁)) (((ℓ - i : ℕ) : ℝ) / 2)
    have hsB := isSmooth_tw (isSmooth_derivB ψ (ℓ - i) _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast
      (Nat.sub_add_cancel h.2).symm hs₂)) ((i : ℝ) / 2)
    have hlA := lfin_tw (hLF ψ hc (r - i) i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast (Nat.sub_add_cancel h.1).symm hs₁)
      (isAdm_cast (Nat.sub_add_cancel h.1).symm ha₁)) (((ℓ - i : ℕ) : ℝ) / 2)
    have hlB := lfin_tw (hLF ψ hc (t - (ℓ - i)) (ℓ - i) _
      (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast (Nat.sub_add_cancel h.2).symm hs₂)
      (isAdm_cast (Nat.sub_add_cancel h.2).symm ha₂)) ((i : ℝ) / 2)
    obtain ⟨cA, cB, hcc, ⟨a, ha0, hea⟩, b, hb0, heb⟩ := hE _ _ _ _ hsA hsB hlA hlB x c f hf0 hf
    exact ⟨i, h, cA, cB, hi, hcc, ⟨a, ha0, hea⟩, b, hb0, heb⟩
  · exfalso
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    apply hw0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show u.1 ∈ (F (i + 1)).toSubmodule
    rw [← hp]
    exact u.2

end PositivityTheory.RgUd.Prod.Pos
