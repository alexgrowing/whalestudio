import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RanksFourToFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.TwBridge.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymBridge GlobalTheory.SymTieExists

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unram (ϖ : kˣ) (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (c : ℂˣ) : ∃ η : kˣ →* ℂˣ, IsUnram η ∧ η ϖ = c := by
  let v : kˣ →* (ValueGroupWithZero k)ˣ := Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom
  have hv : ∀ x : kˣ, ((v x : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) = valuation k (x : k) := fun _ => rfl
  have h1 : valuation k (ϖ : k) < 1 := (hϖ _).2 le_rfl
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  obtain ⟨g, hg⟩ := hom_extend units_roots (zmultiplesHom (Additive (ValueGroupWithZero k)ˣ) (Additive.ofMul (v ϖ)))
    (fun a b h => by
      have h2 : (v ϖ) ^ a = (v ϖ) ^ b := congrArg Additive.toMul h
      have h3 := congrArg (Units.val) h2
      rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, hv] at h3
      exact zpow_right_injective₀ h0 h1.ne h3) (zmultiplesHom (Additive ℂˣ) (Additive.ofMul c))
  refine ⟨(MonoidHom.toAdditive.symm g).comp v, fun x hx => ?_, ?_⟩
  · have : v x = 1 := Units.ext (by rw [hv, hx]; rfl)
    rw [MonoidHom.comp_apply, this, map_one]
  · have := congrArg Additive.toMul (hg 1)
    simpa using this

end Local

section Add
variable {E K k : Type} [Field E] [NumberField E] [Field K]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_psi (P : HeightOneSpectrum (𝓞 E)) (q D : ℕ) (ι : E →+* k) (ϖ : kˣ) (σ₀ : K →+* ℂ) (psi : E → K)
    (hc : IsCompl P q ι ϖ) (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (hD : 1 ≤ D)
    (hadd : ∀ x y, IntAt P ((q : E) ^ D * x) → IntAt P ((q : E) ^ D * y) → psi (x + y) = psi x * psi y)
    (hint : ∀ x, IntAt P x → psi x = 1) (hne : psi ((q : E)⁻¹) ≠ 1) :
    ∃ ψ : AddChar k Circle, HasConductor ψ 1 ∧ ∀ a, IntAt P ((q : E) ^ D * a) → (ψ (ι a) : ℂ) = σ₀ (psi a) := by
  have hq := ComplRes.q_ne_zero hc
  let A : AddSubgroup E := (𝒪[k].toAddSubgroup.comap ι.toAddMonoidHom).comap (AddMonoidHom.mulLeft ((q : E) ^ D))
  have hA : ∀ a, a ∈ A ↔ IntAt P ((q : E) ^ D * a) := fun a => hc.int _
  have h0 : psi 0 = 1 := hint 0 ((hc.int 0).1 (by simp))
  have hpow : ∀ (n : ℕ) (a : A), psi (n • (a : E)) = psi a ^ n := by
    intro n a
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [succ_nsmul, hadd _ _ ((hA _).1 (A.nsmul_mem a.2 n)) ((hA _).1 a.2), ih, pow_succ]
  have hq' : q ^ D ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hq)
  have hnorm : ∀ a : A, ‖σ₀ (psi a)‖ = 1 := fun a => by
    have h1 : psi a ^ (q ^ D) = 1 := by
      rw [← hpow, hint]
      simpa [nsmul_eq_mul] using (hA _).1 a.2
    have h2 : ‖σ₀ (psi a)‖ ^ (q ^ D) = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hq').1 h2
  let f : A →+ Additive Circle :=
    { toFun := fun a => Additive.ofMul ⟨σ₀ (psi a), by simpa [Submonoid.unitSphere] using hnorm a⟩
      map_zero' := congrArg Additive.ofMul (Subtype.ext (by simp [h0]))
      map_add' := fun a b => congrArg Additive.ofMul (Subtype.ext (by
        change σ₀ (psi ((a : E) + b)) = σ₀ (psi a) * σ₀ (psi b)
        rw [hadd _ _ ((hA _).1 a.2) ((hA _).1 b.2), map_mul])) }
  have hf : ∀ a : A, ((Additive.toMul (f a) : Circle) : ℂ) = σ₀ (psi a) := fun _ => rfl
  let j : A →+ k ⧸ 𝒪[k].toAddSubgroup := (QuotientAddGroup.mk' _).comp (ι.toAddMonoidHom.comp A.subtype)
  have hker : j.ker ≤ f.ker := fun a ha => by
    have h1 : ι a ∈ 𝒪[k] := (QuotientAddGroup.eq_zero_iff _).1 ha
    refine congrArg Additive.ofMul (Subtype.ext ?_)
    change σ₀ (psi a) = 1
    rw [hint _ ((hc.int _).1 h1), map_one]
  obtain ⟨g, hg⟩ := hom_extend circle_roots (QuotientAddGroup.kerLift j) (QuotientAddGroup.kerLift_injective j)
    (QuotientAddGroup.lift _ f hker)
  let ψ : AddChar k Circle := AddChar.toAddMonoidHomEquiv.symm (g.comp (QuotientAddGroup.mk' _))
  have hv : ∀ a, IntAt P ((q : E) ^ D * a) → (ψ (ι a) : ℂ) = σ₀ (psi a) := fun a ha => by
    have := hg (QuotientAddGroup.mk ⟨a, (hA a).2 ha⟩)
    rw [QuotientAddGroup.kerLift_mk, QuotientAddGroup.lift_mk] at this
    rw [← hf ⟨a, (hA a).2 ha⟩, ← this]
    rfl
  refine ⟨ψ, fun x => ⟨fun h => ?_, fun h y hy => ?_⟩, hv⟩
  · by_contra hx
    rw [Units.val_one, map_one, not_le] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hxi : valuation k x⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hx
    have h2 := (hϖ _).1 hxi
    have h3 : valuation k (ϖ : k)⁻¹ ≤ valuation k x := by
      rw [map_inv₀] at h2 ⊢
      exact inv_le_of_inv_le₀ (by simp [zero_lt_iff, hx0]) h2
    have h4 := h _ h3
    have h5 : IntAt P ((q : E) ^ D * (q : E)⁻¹) := by
      obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
      rw [pow_succ, mul_inv_cancel_right₀ hq]
      have := ComplRes.intAt_coe (P := P) ((q : 𝓞 E) ^ d)
      simpa using this
    have h6 := hv _ h5
    rw [map_inv₀, ← hc.unif, h4] at h6
    exact hne (σ₀.injective (by rw [← h6]; simp))
  · have hy1 : y ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by simpa using hy.trans h)
    have : (QuotientAddGroup.mk' 𝒪[k].toAddSubgroup) y = 0 := (QuotientAddGroup.eq_zero_iff _).2 hy1
    change Additive.toMul (g ((QuotientAddGroup.mk' 𝒪[k].toAddSubgroup) y)) = 1
    rw [this, map_zero]
    rfl

omit [Field K] in

theorem exists_delta (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ) (hc : IsCompl P q ι ϖ)
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* ℂˣ) :
    ∃ δ : kˣ →* ℂˣ, IsTame δ ∧ ∀ a (u : kˣ), IntAt P a → ∀ hu : IsUnit (redP P a), (u : k) = ι a → δ u = χ hu.unit := by
  obtain ⟨r, hr, h0, hred⟩ := exists_residue P ι hc.int hc.dense
  obtain ⟨μ, hμ, hμv⟩ := exists_tame r (fun x => (h0 x).2) χ
  refine ⟨μ, hμ, fun a u ha hu e => ?_⟩
  let x : 𝒪[k] := ⟨ι a, (hc.int a).2 ha⟩
  have hx : IsUnit x := by
    by_contra h
    have h1 := (h0 x).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h)
    rw [hred] at h1
    haveI := P.isPrime
    exact hu.ne_zero h1
  have e1 : Units.map (𝒪[k]).subtype.toMonoidHom hx.unit = u := Units.ext e.symm
  have e2 : Units.map r.toMonoidHom hx.unit = hu.unit := Units.ext (hred a _)
  rw [← e1, hμv, e2]

end Add

section Tw
variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)

theorem exists_atTwist (s : ℕ) (hP : P.1 ∉ Pr.vGs) (hs : R.m = s + 2) (hok : cst.Ok) (hmu : ∀ i, i < R.m → cst.muq (i + 1) P ≠ 0)
    (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2) :
    ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : X.E →+* k)
      (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W := by
  classical
  letI := GlobalTheory.LocalData.complRel P.1
  haveI := GlobalTheory.LocalData.isLocalField P.1
  obtain ⟨ϖ, hc, hu⟩ := GlobalTheory.AtTypeExists.exists_compl P.1 hq
  obtain ⟨ψ, hψ, hψv⟩ := exists_psi P.1 (qOf P.1) (cst.D P) _ ϖ σ₀ (cst.psi P) hc hu (hok.D_pos P) (hok.psi_add P)
    (hok.psi_int P) (hok.psi_ne P)
  obtain ⟨δ, hδ, hδv⟩ := exists_delta P.1 (qOf P.1) _ ϖ hc
    ((Units.map σ₀.toMonoidHom).comp (resChar (mu : Chr X.F X.E X.K) P.1))⁻¹
  choose η hη hηv using fun i => exists_unram ϖ hu
    (if h : σ₀ (cst.muq i P) = 0 then 1 else Units.mk0 _ h * (δ ϖ)⁻¹)
  have hq0 : (Real.sqrt (qOf P.1) : ℂ) ≠ 0 := by
    have := ComplRes.q_ne_zero hc
    have h2 : 0 < qOf P.1 := Nat.pos_of_ne_zero fun h => this (by rw [h]; simp)
    exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast h2)).ne'
  refine ⟨_, _, _, _, inferInstance, _, ⟨ϖ, hu, ψ, hψ.continuous, hψ, δ, hδ, η, hη, σ₀ (cst.sq P) / Real.sqrt (qOf P.1)⟩,
    hP, hs, hc, hψv, fun a u ha hu' e => ?_, fun i hi => ?_, (div_mul_cancel₀ _ hq0).symm⟩
  · change (δ u : ℂ) = _
    rw [hδv a u ha hu' e, LocE.unitV, dif_pos hu']
    simp
  · change ((η (i + 1) * δ) ϖ : ℂ) = _
    have h : σ₀ (cst.muq (i + 1) P) ≠ 0 := (map_ne_zero σ₀).2 (hmu i hi)
    rw [MonoidHom.mul_apply, hηv, dif_neg h]
    simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  (s : ℕ) (W : TwData k)

theorem sg_sq (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) (hok : cst.Ok) : W.sg ^ 2 = 1 := by
  have h1 := congrArg σ₀ (hok.sq_sq P)
  have hq := ComplRes.q_ne_zero h.compl
  have hq' : (qOf P.1 : ℂ) ≠ 0 := fun h0 => hq (by rw [show qOf P.1 = 0 by exact_mod_cast h0]; simp)
  rw [map_pow, h.sq, mul_pow, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h1
  exact mul_right_cancel₀ hq' (by simpa using h1)

theorem not_isUnram (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) (hξ : resChar (mu : Chr X.F X.E X.K) P.1 ≠ 1) :
    ¬ IsUnram W.δ := by
  intro hun
  refine hξ (MonoidHom.ext fun c => ?_)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.E ⧸ P.1.asIdeal)
  have hr : redP P.1 (a : X.E) = c := by
    have := ComplRes.reduction_spec (P := P.1) (a := (a : X.E)) (r := a) (s := 1) (one_notMem _) (by simp)
    simpa [ha] using this
  have hi := ComplRes.intAt_coe (P := P.1) a
  have hu : IsUnit (redP P.1 (a : X.E)) := hr ▸ c.isUnit
  have hv := (ComplRes.v_eq_one_iff_red h.compl W.unif hi).2 hu
  have h0 : ι a ≠ 0 := fun h0 => by simp [h0] at hv
  have h1 := h.del a (Units.mk0 _ h0) hi hu rfl
  rw [hun _ hv, LocE.unitV, dif_pos hu, show hu.unit = c from Units.ext hr] at h1
  refine Units.ext (σ₀.injective ?_)
  simpa using (inv_eq_one.1 h1.symm)

theorem isGL_existsUnique (j c : ℕ) (hc : cOf R j = c) (γ : AutY X R j) :
    ∃! g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k, IsGL ι γ g := by
  subst hc
  obtain ⟨d, hd⟩ := GlobalTheory.AtTypeExists.exists_ord.1 R.k R.t j
  obtain ⟨e, he⟩ := GlobalTheory.AtTypeExists.exists_ord.2.2.1 _ (R.N j) (cOf R j) _ d hd
  have key : ∀ a b : AutY X R j, toLoc ι e e a.toLinearMap * toLoc ι e e b.toLinearMap = toLoc ι e e (a * b).toLinearMap := by
    intro a b
    ext i l
    have : b (Pi.single (e l) 1) = ∑ m, b (Pi.single (e l) 1) (e m) • (Pi.single (e m) 1 : Fin _ → X.E) := by
      rw [Equiv.sum_comp e (fun m => b (Pi.single (e l) 1) m • (Pi.single m 1 : Fin _ → X.E))]
      ext z; simp [Finset.sum_apply, Pi.single_apply]
    change ∑ m, ι (a (Pi.single (e m) 1) (e i)) * ι (b (Pi.single (e l) 1) (e m)) = ι (a (b (Pi.single (e l) 1)) (e i))
    conv_rhs => rw [this]
    simp [Finset.sum_apply, mul_comm]
  have one : toLoc ι e e (1 : AutY X R j).toLinearMap = 1 := by
    ext i l
    change ι ((Pi.single (e l) 1 : Fin _ → X.E) (e i)) = _
    simp [Pi.single_apply, Matrix.one_apply, apply_ite ι]
  refine ⟨⟨toLoc ι e e γ.toLinearMap, toLoc ι e e (γ⁻¹).toLinearMap, by rw [key, mul_inv_cancel, one],
    by rw [key, inv_mul_cancel, one]⟩, ⟨e, he, rfl⟩, ?_⟩
  rintro g ⟨e', he', hg⟩
  obtain rfl : e' = e := Equiv.ext fun a => Fin.ext ((he' a).trans (he a).symm)
  exact Units.ext hg

end Tw

section Sign
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  (s : ℕ) (W : TwData k)

theorem valuation_spec (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) {a : X.E} (ha : a ≠ 0) :
    IntAt P.1 (a / (qOf P.1 : X.E) ^ LocE.vP P.1 (qOf P.1) a) ∧
      IsUnit (redP P.1 (a / (qOf P.1 : X.E) ^ LocE.vP P.1 (qOf P.1) a)) := by
  have hq := GlobalTheory.AtTypeExists.valuation_norm P.1 (ComplRes.q_not_mem_sq h.compl W.unif)
  have hex : ∃ z : ℤ, IsUnit (redP P.1 (a / (qOf P.1 : X.E) ^ z)) := by
    have h0 : P.1.valuation X.E a ≠ 0 := by simpa using ha
    refine ⟨-WithZero.log (P.1.valuation X.E a), ?_⟩
    set b := a / (qOf P.1 : X.E) ^ (-WithZero.log (P.1.valuation X.E a)) with hb
    have h1 : P.1.valuation X.E b = 1 := by
      rw [hb, map_div₀, map_zpow₀, hq, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log h0, h0]
    have i1 := (GlobalTheory.AtTypeExists.intAt_iff P.1 b).2 h1.le
    have i2 := (GlobalTheory.AtTypeExists.intAt_iff P.1 b⁻¹).2 (by rw [map_inv₀, h1, inv_one])
    have b0 : b ≠ 0 := fun h0 => by simp [h0] at h1
    refine (ComplRes.v_eq_one_iff_red h.compl W.unif i1).1 (le_antisymm (ComplRes.v_le_one h.compl i1) ?_)
    have := ComplRes.v_le_one h.compl i2
    rw [map_inv₀, map_inv₀] at this
    exact (inv_le_one₀ (by simpa [zero_lt_iff] using b0)).1 this
  have hu := Classical.epsilon_spec hex
  refine ⟨?_, hu⟩
  by_contra hn
  have : redP P.1 (a / (qOf P.1 : X.E) ^ LocE.vP P.1 (qOf P.1) a) = 0 :=
    dif_neg fun ⟨_, r, t, ht, e, _⟩ => hn ⟨r, t, ht, e⟩
  exact hu.ne_zero this

theorem mu_agree (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) (i : ℕ) (hi : i < R.m) {a : X.E} (u : kˣ) (hu : (u : k) = ι a) :
    ((W.T s R).mu (i + 1) u : ℂ) = σ₀ (muAt Ch sel mu cst i P a) := by
  have ha : a ≠ 0 := fun h0 => u.ne_zero (by rw [hu, h0, map_zero])
  obtain ⟨h1, h2⟩ := valuation_spec sel mu cst σ₀ P ι s W h ha
  set z := LocE.vP P.1 (qOf P.1) a with hz
  have e : ((u * W.ϖ ^ (-z) : kˣ) : k) = ι (a / (qOf P.1 : X.E) ^ z) := by
    rw [map_div₀, map_zpow₀, ← h.compl.unif, ← hu]; simp [div_eq_mul_inv]
  have h3 := h.del _ _ h1 h2 e
  have h4 := W.unr (i + 1) _ (by rw [e]; exact (ComplRes.v_eq_one_iff_red h.compl W.unif h1).2 h2)
  have h5 : u = W.ϖ ^ z * (u * W.ϖ ^ (-z)) := by simp [mul_comm u]
  change ((W.η (i + 1) * W.δ) u : ℂ) = _
  rw [h5, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, h.mu i hi, MonoidHom.mul_apply, h4, one_mul, h3,
    muAt, LocE.locChar, if_neg h.nmem, ← hz, map_mul, map_zpow₀, LocE.unitV, LocE.unitV, dif_pos h2, dif_pos h2]
  simp

theorem nabs_agree (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) (hok : cst.Ok) {a : X.E} (u : kˣ) (hu : (u : k) = ι a) (n : ℕ) :
    ((nabs k u ^ ((n : ℝ) / 2) : ℝ) : ℂ) =
        W.sg ^ (LocE.vP P.1 (qOf P.1) a * n) * σ₀ (cst.sq P ^ (-LocE.vP P.1 (qOf P.1) a * n)) ∧
      ((nabs k u ^ (-(n : ℝ) / 2) : ℝ) : ℂ) =
        W.sg ^ (LocE.vP P.1 (qOf P.1) a * n) * σ₀ (cst.sq P ^ (LocE.vP P.1 (qOf P.1) a * n)) := by
  have ha : a ≠ 0 := fun h0 => u.ne_zero (by rw [hu, h0, map_zero])
  obtain ⟨h1, h2⟩ := valuation_spec sel mu cst σ₀ P ι s W h ha
  set z := LocE.vP P.1 (qOf P.1) a with hz
  have e : ((u * W.ϖ ^ (-z) : kˣ) : k) = ι (a / (qOf P.1 : X.E) ^ z) := by
    rw [map_div₀, map_zpow₀, ← h.compl.unif, ← hu]; simp [div_eq_mul_inv]
  have h4 := nabs_eq_one_of_valuation_eq_one (x := u * W.ϖ ^ (-z))
    (by rw [e]; exact (ComplRes.v_eq_one_iff_red h.compl W.unif h1).2 h2)
  have hlt := ComplRes.v_unif_lt_one W.unif
  have hirr : Irreducible (⟨W.ϖ, (Valuation.mem_integer_iff _ _).2 hlt.le⟩ : 𝒪[k]) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one, W.unif,
      Ideal.mem_span_singleton, (Valuation.integer.integers (valuation k)).dvd_iff_le]
    rfl
  have h6 := nabs_uniformiser hirr (x := W.ϖ) rfl
  rw [ComplRes.resCard_eq h.compl W.unif] at h6
  have hq := ComplRes.q_ne_zero h.compl
  have hq0 : (0 : ℝ) < qOf P.1 := by
    exact_mod_cast Nat.pos_of_ne_zero fun h0 => hq (by rw [h0]; simp)
  have h7 : nabs k u = (qOf P.1 : ℝ) ^ (-z) := by
    have : nabs k (u * W.ϖ ^ (-z)) = nabs k u * nabs k W.ϖ ^ (-z) := by simp [nabs]
    rw [h4, h6, _root_.inv_zpow', neg_neg] at this
    rw [_root_.zpow_neg]
    exact eq_inv_of_mul_eq_one_left this.symm
  have hs := sg_sq sel mu cst σ₀ P ι s W h hok
  have hs0 : W.sg ≠ 0 := fun h0 => by simp [h0] at hs
  have key : ∀ t : ℤ, (((qOf P.1 : ℝ) ^ ((t : ℝ) / 2) : ℝ) : ℂ) = W.sg ^ t * σ₀ (cst.sq P ^ t) := fun t => by
    rw [map_zpow₀, h.sq, mul_zpow, ← mul_assoc, ← mul_zpow, ← pow_two, hs, _root_.one_zpow, one_mul, ← Complex.ofReal_zpow,
      Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
    congr 2; ring
  have hneg : ∀ t : ℤ, W.sg ^ (-t) = W.sg ^ t := fun t => by
    rw [_root_.zpow_neg]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← mul_zpow, ← pow_two, hs, _root_.one_zpow]
  constructor
  · rw [← hneg, ← neg_mul, ← key, h7, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
    congr 2; push_cast; ring
  · rw [← key, h7, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
    congr 2; push_cast; ring

theorem toLoc_eq {A B : Type} {a b : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (x : (Fin b → X.E) →ₗ[X.E] (Fin a → X.E)) :
    toLoc ι e e' x = ((LinearMap.toMatrix' x).map ι).submatrix e e' := by
  ext i l; simp [toLoc, LinearMap.toMatrix'_apply]

theorem toLoc_mul {A B C : Type} [Fintype B] {a b c : ℕ} (e : A ≃ Fin a) (e' : B ≃ Fin b) (e'' : C ≃ Fin c)
    (x : (Fin b → X.E) →ₗ[X.E] (Fin a → X.E)) (y : (Fin c → X.E) →ₗ[X.E] (Fin b → X.E)) :
    toLoc ι e e' x * toLoc ι e' e'' y = toLoc ι e e'' (x ∘ₗ y) := by
  rw [toLoc_eq, toLoc_eq, toLoc_eq, submatrix_mul_equiv, LinearMap.toMatrix'_comp, Matrix.map_mul]

theorem det_toLoc {A : Type} [Fintype A] [DecidableEq A] {a : ℕ} (e : A ≃ Fin a) (γ : (Fin a → X.E) ≃ₗ[X.E] (Fin a → X.E))
    (g : GL A k) (hg : g.val = toLoc ι e e γ.toLinearMap) :
    ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = ι (LinearEquiv.det γ : X.Eˣ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hg, toLoc_eq, det_submatrix_equiv_self, LinearEquiv.coe_det,
    ← LinearMap.det_toMatrix', RingHom.map_det]
  rfl

theorem om_agree (h : AtTwist (R := R) sel mu cst σ₀ P ι s W) (hok : cst.Ok) (j c c' : ℕ) (hj : j < R.m)
    (e' : XIx (Fin R.k) (Fin R.t) j ⊕ Fin c' ≃ Fin (R.N j + cOf R j))
    (e : XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin c ≃ Fin (R.N (j + 1) + cOf R (j + 1)))
    (a : AutY X R j) (b : AutY X R (j + 1)) (g : GL _ k) (g' : GL _ k) (hg : g.val = toLoc ι e' e' a.toLinearMap)
    (hg' : g'.val = toLoc ι e e b.toLinearMap) (Φ : Matrix _ _ k → ℂ) (ΦE : Loc.SF X.E X.K _ _)
    (hΦ : ∀ x, Φ (toLoc ι e e' x) = σ₀ (ΦE x)) (x) :
    om ((W.T s R).mu (j + 1)) g g' Φ (toLoc ι e e' x) =
      sgn sel mu P W a (R.N (j + 1) + cOf R (j + 1)) * sgn sel mu P W b (R.N j + cOf R j) *
        σ₀ (Loc.om (muAt Ch sel mu cst j P) (LocE.vP P.1 (qOf P.1)) (cst.sq P) a b ΦE x) := by
  have d := det_toLoc ι e' a g hg
  have d' := det_toLoc ι e b g' hg'
  have hi : (g'⁻¹).val = toLoc ι e e b.symm.toLinearMap := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hg', toLoc_mul, LinearEquiv.comp_symm, toLoc_eq]
    simp
  unfold om Loc.om sgn
  rw [hi, hg, toLoc_mul, toLoc_mul, hΦ, Units.val_inv_eq_inv_val, mu_agree Ch sel mu cst σ₀ P ι s W h j hj _ d,
    mu_agree Ch sel mu cst σ₀ P ι s W h j hj _ d', Fintype.card_congr e, Fintype.card_congr e', Fintype.card_fin, Fintype.card_fin,
    (nabs_agree sel mu cst σ₀ P ι s W h hok _ d _).1, (nabs_agree sel mu cst σ₀ P ι s W h hok _ d' _).2]
  simp only [map_mul, map_inv₀, LinearMap.comp_assoc]
  ring

end Sign

theorem twData_closed : ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (W : TwData k), ¬ IsUnram W.δ ∧ (∀ j, W.η j ≠ 1) ∧ W.sg = -1 := by
  obtain ⟨X, Pr, R, Ch, sel, S₀, mu, cst, σ₀, P, k, i1, i2, i3, i4, ι, s, S, -, -, -, -, hχ, -, hS⟩ :=
    GlobalTheory.AtTypeClosed.exists_closed_ok
  obtain ⟨η, hη, hηv⟩ := exists_unram S.ϖ S.unif (-1)
  refine ⟨k, i1, i2, i3, i4, ⟨S.ϖ, S.unif, S.ψ, S.cond.continuous, S.cond, S.μ 1, S.tame 1, fun _ => η, fun _ => hη, -1⟩,
    fun hun => ?_, fun _ h => ?_, rfl⟩
  · refine hχ (MonoidHom.ext fun c => ?_)
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 X.E ⧸ P.1.asIdeal)
    have hr : redP P.1 (a : X.E) = c := by
      have := ComplRes.reduction_spec (P := P.1) (a := (a : X.E)) (r := a) (s := 1) (one_notMem _) (by simp)
      simpa [ha] using this
    have hi := ComplRes.intAt_coe (P := P.1) a
    have hu : IsUnit (redP P.1 (a : X.E)) := hr ▸ c.isUnit
    have hv := (ComplRes.v_eq_one_iff_red hS.tie.compl S.unif hi).2 hu
    have h0 : ι a ≠ 0 := fun h0 => by simp [h0] at hv
    have h1 := hS.tie.chi 0 a (Units.mk0 _ h0) hi hu rfl
    have h2 : S.μ (0 + 1) (Units.mk0 _ h0) = 1 := hun _ hv
    rw [h2, LocE.unitV, dif_pos hu, show hu.unit = c from Units.ext hr] at h1
    refine Units.ext (σ₀.injective ?_)
    simpa using h1.symm
  · have h1 : η = 1 := h
    rw [h1] at hηv
    have := congrArg Units.val hηv
    norm_num at this

end GlobalTheory.TwBridge.Model
