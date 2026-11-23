import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.HkComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.HkReps
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.MemParahoricTimesPrincipalCongruenceIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HolWCAux

open UpperTheory.Esk

variable {F : Type} [Field F] [NumberField F]

def rt (I : Type) : Representation ℂ (GF F) (X I × GF F → ℂ) where
  toFun g :=
    { toFun := fun f p => f (p.1, p.2 * g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext f p; simp
  map_mul' g h := by ext f p; simp [mul_assoc]

theorem rt_apply (I : Type) (g : GF F) (f : X I × GF F → ℂ) (p : X I × GF F) : rt I g f p = f (p.1, p.2 * g) := rfl

theorem op_eq {I : Type} [Fintype I] {n : ℕ} (a : Fin n → GF F) (f : X I × GF F → ℂ) :
    Dat.Op a f = ∑ i, rt I (a i) f := by
  funext p
  show (∑ i, f (p.1, p.2 * a i)) = _
  simp [Finset.sum_apply, rt_apply]

theorem wordU {I : Type} [Fintype I] {c : Pl F → ℕ} (Mk : Submodule ℂ (X I × GF F → ℂ))
    (hfix : ∀ f ∈ Mk, f ∈ Hi.fixd (rt I) (Kc c)) (z : Pl F → ℂ) (na : Pl F → ℕ) (aw : ∀ w, Fin (na w) → GF F)
    (haw : ∀ w, IsReps c [w] (aw w)) (hw : ∀ w, ∀ f ∈ Mk, Dat.Op (aw w) f ∈ Mk) (W : List (Pl F)) (f : Mk) :
    (((W.map fun w => z w • (Dat.Op (aw w)).restrict (hw w)).prod f : Mk) : X I × GF F → ℂ) =
      (W.map z).prod • (W.map fun w => Uop w ((rt I).comp (locGL F 2 w)) (c w)).prod (f : X I × GF F → ℂ) := by
  induction W with
  | nil => simp
  | cons w W ih =>
    have key : ∀ g : Mk, ((z w • (Dat.Op (aw w)).restrict (hw w)) g : X I × GF F → ℂ) =
        z w • Uop w ((rt I).comp (locGL F 2 w)) (c w) (g : X I × GF F → ℂ) := by
      intro g
      have h := ((haw w).act _ (rt I) _ (hfix _ g.2)).2
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
      rw [LinearMap.smul_apply, Submodule.coe_smul, LinearMap.coe_restrict_apply, op_eq, h]
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [key, ih, map_smul, mul_smul]

theorem word {I : Type} [Fintype I] {c : Pl F → ℕ} (Mk : Submodule ℂ (X I × GF F → ℂ))
    (hfix : ∀ f ∈ Mk, f ∈ Hi.fixd (rt I) (Kc c)) (z : Pl F → ℂ) (na : Pl F → ℕ) (aw : ∀ w, Fin (na w) → GF F)
    (haw : ∀ w, IsReps c [w] (aw w)) (hw : ∀ w, ∀ f ∈ Mk, Dat.Op (aw w) f ∈ Mk) (W : List (Pl F)) {n : ℕ}
    (a : Fin n → GF F) (ha : IsReps c W a) (h : ∀ f ∈ Mk, Dat.Op a f ∈ Mk) :
    (W.map fun w => z w • (Dat.Op (aw w)).restrict (hw w)).prod = (W.map z).prod • (Dat.Op a).restrict h := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  rw [wordU Mk hfix z na aw haw hw W f, LinearMap.smul_apply, Submodule.coe_smul, LinearMap.coe_restrict_apply, op_eq,
    (ha.act _ (rt I) _ (hfix _ f.2)).2]

theorem comm {I : Type} [Fintype I] {c : Pl F → ℕ} (hc : HkComm) (Mk : Submodule ℂ (X I × GF F → ℂ))
    (hfix : ∀ f ∈ Mk, f ∈ Hi.fixd (rt I) (Kc c)) (z : Pl F → ℂ) (na : Pl F → ℕ) (aw : ∀ w, Fin (na w) → GF F)
    (haw : ∀ w, IsReps c [w] (aw w)) (hw : ∀ w, ∀ f ∈ Mk, Dat.Op (aw w) f ∈ Mk) (i j : Pl F) :
    (z i • (Dat.Op (aw i)).restrict (hw i)) * (z j • (Dat.Op (aw j)).restrict (hw j)) =
      (z j • (Dat.Op (aw j)).restrict (hw j)) * (z i • (Dat.Op (aw i)).restrict (hw i)) := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  have h1 := wordU Mk hfix z na aw haw hw [i, j] f
  have h2 := wordU Mk hfix z na aw haw hw [j, i] f
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h1 h2
  rw [h1, h2, mul_comm (z i) (z j), Module.End.mul_apply, Module.End.mul_apply, (hc F _ (rt I) c f.1 (hfix _ f.2) i).2 j]

theorem fix_of_form [IsTotallyReal F] {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ)
    {k : InfinitePlace F → ℕ} {f : X (InfinitePlace F) × GF F → ℂ} (hf : (mkDat c χ).IsForm k f) :
    f ∈ Hi.fixd (rt (InfinitePlace F)) (Kc c) := by
  change ∀ u ∈ Kc c, rt _ u f = f
  intro u hu
  funext p
  have hH : u ∈ Hc c := Subgroup.mem_sup_left hu
  have h1 : χ ⟨u, hH⟩ = 1 := by
    rw [(hχ ⟨u, hH⟩).2 u hu 1 (by simp)]
    simp
  have := hf.lev p.1 p.2 ⟨u, hH⟩
  change f (p.1, p.2 * u) = ((χ ⟨u, hH⟩ : ℂˣ) : ℂ) * f (p.1, p.2) at this
  rw [h1, Units.val_one, one_mul] at this
  rw [rt_apply, this]

theorem eig_iff [IsTotallyReal F] (hRel : HRel) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {w : Pl F} {n : ℕ}
    {a : Fin n → GF F} (ha : IsReps c [w] a) {f : X (InfinitePlace F) × GF F → ℂ} {φ : TR.Sm F 2} (hrel : Rel k f φ.1)
    (hφ : φ ∈ Hi.fixd (TR.finRep F 2) (Kc c)) (α β : ℂ) :
    α • Dat.Op a f = β • f ↔ α • Uop w (locSm F w) (c w) φ = β • φ := by
  obtain ⟨-, h2, h3, h4, h0, h5⟩ := hRel F k
  have hsm : ∀ {g : X (InfinitePlace F) × GF F → ℂ} {ψ : GA F 2 → ℂ} (s : ℂ), Rel k g ψ → Rel k (s • g) (s • ψ) :=
    fun s h => by simpa using h4 0 _ 0 _ s h0 h
  have hU : (∑ i, TR.finRep F 2 (a i) φ) = Uop w (locSm F w) (c w) φ := by
    have := (ha.act (TR.Sm F 2) (TR.finRep F 2) φ hφ).2
    simpa [locSm] using this
  have r1 : Rel k (α • Dat.Op a f) ((α • Uop w (locSm F w) (c w) φ : TR.Sm F 2) : GA F 2 → ℂ) := by
    rw [← hU]; simpa using hsm α (h5 n a f φ hrel)
  have r2 : Rel k (β • f) ((β • φ : TR.Sm F 2) : GA F 2 → ℂ) := by simpa using hsm β hrel
  constructor
  · intro h
    rw [h] at r1
    exact Subtype.ext (h2 _ _ _ r1 r2)
  · intro h
    rw [h] at r1
    exact h3 _ _ _ r1 r2

theorem lift [IsTotallyReal F] (hH0 : H0) (hRel : HRel) (hH2a : H2a) (hH2d : H2d) (hH2e : H2e)
    {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} (hc : {w | c w ≠ 0}.Finite) {ω : HChar F} (hω : IsOfFinOrder ω)
    {χ : Hc c →* ℂˣ} (hχ : IsChi c ω χ) (hS : Sgn k ω) (h1 : ∀ v, 1 ≤ k v)
    {f : X (InfinitePlace F) × GF F → ℂ} (hf : (mkDat c χ).IsForm k f) (hf0 : f ≠ 0)
    (na : Pl F → ℕ) (aw : ∀ w, Fin (na w) → GF F) (haw : ∀ w, IsReps c [w] (aw w)) (α s : Pl F → ℂ)
    (heig : ∀ w, α w • Dat.Op (aw w) f = s w • f) :
    ∃ φ' : TR.Sm F 2, IsHolV k c ω φ' ∧ φ' ≠ 0 ∧ TR.IsCuspForm φ' ∧
      ∀ w, α w • Uop w (locSm F w) (c w) φ' = s w • φ' := by
  obtain ⟨ψ, hψ⟩ := (hRel F k).1 f
  obtain ⟨hψS, hhol⟩ := hH2d F k c hc ω χ hω hχ hS h1 f ψ hf hψ
  have hne : (⟨ψ, hψS⟩ : TR.Sm F 2) ≠ 0 := by
    intro h
    apply hf0
    have h' : ψ = 0 := congrArg Subtype.val h
    rw [h'] at hψ
    exact (hRel F k).2.2.1 _ _ _ hψ (hRel F k).2.2.2.2.1
  refine ⟨⟨ψ, hψS⟩, hhol, hne, ?_, ?_⟩
  · exact hH2e F k c ω _ hω h1 hhol (hH2a F k c hc ω χ hω hχ hS h1 f ψ hf hψ).2.2.2
  · intro w
    have hfix := (hH0 F k c ω _ hhol hne).2.1
    exact (eig_iff hRel (haw w) hψ hfix (α w) (s w)).1 (heig w)

theorem nu_nat_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) : nu ι (n : ℂ) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

theorem nu_int_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℤ) : nu ι (n : ℂ) ≤ 1 := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using nu_nat_le ι m
  · rw [Int.cast_neg, Valuation.map_neg]
    simpa using nu_nat_le ι m

theorem nu_coprime {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (hnul : nu ι (l : ℂ) < 1) (m : ℕ) (hm : ¬ l ∣ m) :
    nu ι (m : ℂ) = 1 := by
  have hl := (Fact.out : l.Prime)
  have hcop : Nat.Coprime m l := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)
  have hbez := Nat.gcd_eq_gcd_ab m l
  rw [Nat.Coprime.gcd_eq_one hcop] at hbez
  have hc : ((m : ℂ) * (Nat.gcdA m l : ℂ)) = 1 - (l : ℂ) * (Nat.gcdB m l : ℂ) := by
    have := congrArg (fun x : ℤ => (x : ℂ)) hbez
    push_cast at this
    linear_combination -this
  have h1 : nu ι ((m : ℂ) * (Nat.gcdA m l : ℂ)) = 1 := by
    rw [hc, Valuation.map_one_sub_of_lt]
    rw [map_mul]
    calc nu ι (l : ℂ) * nu ι (Nat.gcdB m l : ℂ) ≤ nu ι (l : ℂ) := mul_le_of_le_one_right (by simp) (nu_int_le ι _)
      _ < 1 := hnul
  rw [map_mul] at h1
  refine le_antisymm (nu_nat_le ι m) ?_
  by_contra hlt
  push Not at hlt
  have : nu ι (m : ℂ) * nu ι (Nat.gcdA m l : ℂ) < 1 :=
    calc _ ≤ nu ι (m : ℂ) := mul_le_of_le_one_right (by simp) (nu_int_le ι _)
      _ < 1 := hlt
  exact absurd h1 this.ne

theorem smul_fix {V : Type} [AddCommGroup V] [Module ℂ V] (A P s : ℂ) (hP : P ≠ 0) (x y : V)
    (h : (A * P) • x = s • y) : A • x = (P⁻¹ * s) • y := by
  rw [mul_smul, ← h, smul_smul, ← mul_assoc, mul_comm P⁻¹ A, mul_assoc, inv_mul_cancel₀ hP, mul_one]

end UpperTheory.Esk.HolWCAux

open UpperTheory.Esk.HolWCAux in
theorem UpperTheory.Esk.pf_HolWC : UpperTheory.Esk.Fin0 → UpperTheory.Esk.FormsStableUnderOperators → UpperTheory.Esk.DAx → UpperTheory.Esk.DReps → UpperTheory.Esk.DGood → UpperTheory.Esk.TrCong → UpperTheory.Esk.H0 → UpperTheory.Esk.H0b → UpperTheory.Esk.HRel → UpperTheory.Esk.H1 → UpperTheory.Esk.HFin → UpperTheory.Esk.H2a → UpperTheory.Esk.H2d → UpperTheory.Esk.H2e → UpperTheory.Esk.HolWC := by
  intro hFin0 hE0b hDAx hReps hGood hTr hH0 hH0b hRel hH1 hHFin hH2a hH2d hH2e
  intro F _ _ _ hd l _ hl2 ι D k₀ hk₀ c hc hcl hu ω hω φ lam hφ hcusp hlam S B
  classical
  have hl := (Fact.out : l.Prime)
  have hk1 : IsHolV (fun _ => k₀) c ω φ := isHolV_of hφ.hol
  obtain ⟨hSgn, hφfix, χ, hχ⟩ := hH0 F (fun _ => k₀) c ω φ hk1 hφ.ne
  obtain ⟨hχfin, -⟩ := hH0b F (fun _ => k₀) c ω χ hω hχ
  have hAx : (mkDat c χ).Ax := hDAx F hd c hc χ hχfin
  have hE : ∀ k, (∀ f, f ∈ (mkDat c χ).M k ↔ (mkDat c χ).IsForm k f) ∧ ∀ (ι : Type) [Fintype ι] (a : ι → GF F),
      (mkDat c χ).Good a → ∀ f ∈ (mkDat c χ).M k, Dat.Op a f ∈ (mkDat c χ).M k := hE0b F _ _ (mkDat c χ) hAx
  choose na aw haw using fun w : Pl F => hReps F c [w]
  have hgood : ∀ w, (mkDat c χ).Good (aw w) := fun w => (hGood F c ω χ hχ [w] (na w) (aw w) (haw w)).1
  have hfixM : ∀ k, ∀ f ∈ (mkDat c χ).M k, f ∈ Hi.fixd (rt (InfinitePlace F)) (Kc c) :=
    fun k f hf => fix_of_form hχ (((hE k).1 f).1 hf)
  have hwM : ∀ k, ∀ w, ∀ f ∈ (mkDat c χ).M k, Dat.Op (aw w) f ∈ (mkDat c χ).M k := fun k w => (hE k).2 _ (aw w) (hgood w)
  have hcomm : HkComm := UpperTheory.V.Sd.Wc.hkComm (UpperTheory.V.Sd.Wc.hkReps UpperTheory.V.Sd.uopSum) UpperTheory.V.Sd.Wc.kcTop
  have : FiniteDimensional ℂ ((mkDat c χ).M fun _ => k₀) :=
    hHFin F (fun _ => k₀) c hc ω χ hω hχ hSgn (fun _ => by omega)
  obtain ⟨N, hN⟩ : ∃ N, N = Module.finrank ℂ ((mkDat c χ).M fun _ => k₀) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (l - 1) * l ^ N * max B 1 := ⟨_, rfl⟩
  have hl1 : 0 < l - 1 := by have := hl.two_le; omega
  have htB : t ≥ B := by
    rw [ht]
    calc B ≤ max B 1 := le_max_left _ _
      _ ≤ (l - 1) * l ^ N * max B 1 := Nat.le_mul_of_pos_left _ (Nat.mul_pos hl1 (pow_pos hl.pos _))
  have htd : l - 1 ∣ t := ⟨l ^ N * max B 1, by rw [ht]; ring⟩
  have hdiv : ∀ v, (l - 1) * l ^ N ∣ (fun v : InfinitePlace F => if v ∈ S then t else 0) v := by
    intro v
    simp only
    split_ifs
    · exact ⟨max B 1, ht⟩
    · exact dvd_zero _
  have hSgn' : Sgn (fun v => k₀ + 2 * (if v ∈ S then t else 0)) ω := by
    intro v
    rw [hSgn v]
    simp [pow_add, pow_mul]
  have hk'1 : ∀ v, 1 ≤ (fun v => k₀ + 2 * (if v ∈ S then t else 0)) v := fun v => by simp only; omega
  have : FiniteDimensional ℂ ((mkDat c χ).M fun v => k₀ + 2 * (if v ∈ S then t else 0)) :=
    hHFin F _ c hc ω χ hω hχ hSgn' hk'1
  have hnul : nu ι (l : ℂ) < 1 := by
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h := (D.lt v ((l : ℕ) : (D.pl v).adicCompletion F)).2 (by
      rw [D.unif v, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    simpa using h
  have hnul0 : 0 < nu ι (l : ℂ) := (Valuation.pos_iff _).2 (by exact_mod_cast hl.ne_zero)
  have hε : ∀ d : ℕ, 1 ≤ d → d ≤ Module.finrank ℂ ((mkDat c χ).M fun _ => k₀) → nu ι (l : ℂ) ^ N < nu ι (d : ℂ) := by
    intro d hd1 hdN
    rw [← hN] at hdN
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : d ≠ 0) l hl.one_lt.ne'
    have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => hm (h ▸ dvd_zero l))
    have ha : a < N := by
      have h1 : l ^ a ≤ l ^ a * m := Nat.le_mul_of_pos_right _ hm0
      have h2 : N < l ^ N := Nat.lt_pow_self hl.one_lt
      by_contra hh
      push Not at hh
      have := Nat.pow_le_pow_right hl.pos hh
      omega
    push_cast
    rw [map_mul, map_pow, nu_coprime ι hnul m hm, mul_one]
    exact pow_lt_pow_right_of_lt_one₀ hnul0 hnul ha
  obtain ⟨f0, hf0, hrel0⟩ := hH1 F (fun _ => k₀) c ω χ hω hχ φ hk1 hcusp
  have hf0M : f0 ∈ (mkDat c χ).M fun _ => k₀ := ((hE _).1 f0).2 hf0
  have hf0ne : (⟨f0, hf0M⟩ : (mkDat c χ).M fun _ => k₀) ≠ 0 := by
    intro h
    have h0 : f0 = 0 := congrArg Subtype.val h
    rw [h0] at hrel0
    apply hφ.ne
    exact Subtype.ext ((hRel F _).2.1 _ _ _ hrel0 (hRel F _).2.2.2.2.1)
  have hnz0 : ∀ w, nz D k₀ 0 w = (((normV w : ℝ) ^ ((k₀ : ℝ) / 2 - 1) : ℝ) : ℂ) := fun w => by simp [nz]
  have heig : ∀ w, (nz D k₀ 0 w • (Dat.Op (aw w)).restrict (hwM (fun _ => k₀) w)) ⟨f0, hf0M⟩ = lam w • ⟨f0, hf0M⟩ := by
    intro w
    apply Subtype.ext
    simp only [LinearMap.smul_apply, Submodule.coe_smul, LinearMap.coe_restrict_apply]
    refine (eig_iff hRel (haw w) hrel0 hφfix _ _).2 ?_
    have := hφ.eig w
    simp only [hk, LinearMap.smul_apply] at this
    rw [hnz0]
    exact this
  have htr : ∀ (W : List (Pl F)) (r : ℕ), 1 ≤ r → (∀ j ∈ Finset.univ.image D.pl, r ≤ W.count j) →
      nu ι (LinearMap.trace ℂ ((mkDat c χ).M fun _ => k₀)
        (W.map fun w => nz D k₀ 0 w • (Dat.Op (aw w)).restrict (hwM (fun _ => k₀) w)).prod) ≤ 1 ∧
      nu ι (LinearMap.trace ℂ ((mkDat c χ).M fun v => k₀ + 2 * (if v ∈ S then t else 0))
        (W.map fun w => nz D k₀ (fun v => if v ∈ S then t else 0) w • (Dat.Op (aw w)).restrict
          (hwM (fun v => k₀ + 2 * (if v ∈ S then t else 0)) w)).prod) ≤ 1 ∧
      nu ι (LinearMap.trace ℂ ((mkDat c χ).M fun _ => k₀)
        (W.map fun w => nz D k₀ 0 w • (Dat.Op (aw w)).restrict (hwM (fun _ => k₀) w)).prod -
        LinearMap.trace ℂ ((mkDat c χ).M fun v => k₀ + 2 * (if v ∈ S then t else 0))
        (W.map fun w => nz D k₀ (fun v => if v ∈ S then t else 0) w • (Dat.Op (aw w)).restrict
          (hwM (fun v => k₀ + 2 * (if v ∈ S then t else 0)) w)).prod) ≤ max (nu ι (l : ℂ) ^ N) (nu ι (l : ℂ) ^ r) := by
    intro W r hr hW
    obtain ⟨n, a, ha⟩ := hReps F c W
    have hg := (hGood F c ω χ hχ W n a ha).1
    have h0 := (hE (fun _ => k₀)).2 _ a hg
    have h1 := (hE (fun v => k₀ + 2 * (if v ∈ S then t else 0))).2 _ a hg
    rw [word _ (hfixM _) (nz D k₀ 0) na aw haw (hwM _) W a ha h0,
      word _ (hfixM _) (nz D k₀ (fun v => if v ∈ S then t else 0)) na aw haw (hwM _) W a ha h1,
      LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    exact hTr F hd l hl2 ι D k₀ hk₀ c hc hcl hu ω χ hω hχ hSgn N (fun v => if v ∈ S then t else 0) hdiv W r hr
      (fun v => hW _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))) n a ha h0 h1
  obtain ⟨f', s', hf'ne, hf'eig, hs'⟩ := hFin0 (nu ι) l hl hnul (Pl F) ((mkDat c χ).M fun _ => k₀)
    ((mkDat c χ).M fun v => k₀ + 2 * (if v ∈ S then t else 0))
    (fun w => nz D k₀ 0 w • (Dat.Op (aw w)).restrict (hwM (fun _ => k₀) w))
    (fun w => nz D k₀ (fun v => if v ∈ S then t else 0) w • (Dat.Op (aw w)).restrict
      (hwM (fun v => k₀ + 2 * (if v ∈ S then t else 0)) w))
    (fun i j => comm hcomm _ (hfixM _) _ na aw haw (hwM _) i j)
    (fun i j => comm hcomm _ (hfixM _) _ na aw haw (hwM _) i j)
    (Finset.univ.image D.pl) (nu ι (l : ℂ) ^ N) (nu ι (l : ℂ)) hnul hε htr ⟨f0, hf0M⟩ lam hf0ne heig
    (fun j hj => by obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hj; exact hlam v)
  have hf'F := ((hE _).1 f'.1).1 f'.2
  have hf'0 : f'.1 ≠ 0 := fun h => hf'ne (Subtype.ext h)
  obtain ⟨φ', hhol, hne, hcusp', hφ'eig⟩ := lift hH0 hRel hH2a hH2d hH2e hc hω hχ hSgn' hk'1 hf'F hf'0 na aw haw
    (fun w => nz D k₀ (fun v => if v ∈ S then t else 0) w) s' (fun w => by
      have := congrArg Subtype.val (hf'eig w)
      simpa only [LinearMap.smul_apply, Submodule.coe_smul, LinearMap.coe_restrict_apply] using this)
  have hP : ∀ w, (∏ v, if D.pl v = w then (l : ℂ) ^ (if v ∈ S then t else 0) else 1) ≠ 0 := fun w =>
    Finset.prod_ne_zero_iff.2 fun v _ => by split_ifs <;> simp [hl.ne_zero]
  refine ⟨t, htB, htd, φ', fun w => (∏ v, if D.pl v = w then (l : ℂ) ^ (if v ∈ S then t else 0) else 1)⁻¹ * s' w,
    hhol, hne, hcusp', ?_, ?_⟩
  · intro w
    have := hφ'eig w
    simp only [nz] at this
    simp only [hk, LinearMap.smul_apply]
    exact smul_fix _ _ _ (hP w) _ _ this
  · intro w
    have hprod : (∏ v, if D.pl v = w ∧ v ∈ S then (l : ℂ) ^ t else 1) =
        ∏ v, if D.pl v = w then (l : ℂ) ^ (if v ∈ S then t else 0) else 1 :=
      Finset.prod_congr rfl fun v _ => by
        by_cases h1 : D.pl v = w <;> by_cases h2 : v ∈ S <;> simp [h1, h2]
    rw [hprod, ← mul_assoc, mul_inv_cancel₀ (hP w), one_mul]
    exact hs' w
