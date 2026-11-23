import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCharacterH1FiniteLevels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitCharacterOfIntegralCyclotomicProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergOrdinaryOfVanishingOnCycloKernel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq.CardOrd

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem span_eq_Ik (c : Coef l) (n : ℕ) : Ideal.span {((l : ℕ) : c.O) ^ n} = Ik c n := by
  ext x
  rw [Ideal.mem_span_singleton, mem_Ik]
  exact (GlobalTheory.Coef.norm_le_norm_pow_iff_dvd l c n x).symm

def levEquiv (c : Coef l) (n : ℕ) : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n) ≃+ Qn c n :=
  (Ideal.quotEquivOfEq (span_eq_Ik c n)).toAddEquiv

theorem levEquiv_mk (c : Coef l) (n : ℕ) (x : c.O) :
    levEquiv c n (UpperTheory.V.X.Lev.mk (((l : ℕ) : c.O) ^ n) x) = red c n x := rfl

theorem card_lev (c : Coef l) (n : ℕ) :
    Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) = Nat.card (Qn c n) :=
  Nat.card_congr (levEquiv c n).toEquiv

theorem levEquiv_smul (c : Coef l) (n : ℕ) (a : c.O) (x : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) :
    levEquiv c n (a • x) = red c n a * levEquiv c n x := by
  obtain ⟨y, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective _ x
  rw [← map_smul, smul_eq_mul, levEquiv_mk, levEquiv_mk, map_mul]

def lineInc (c : Coef l) (n : ℕ) : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n) →+ Mn c n :=
  (AddMonoidHom.single (fun _ : Fin 2 => Qn c n) 0).comp (levEquiv c n).toAddMonoidHom

theorem lineInc_apply (c : Coef l) (n : ℕ) (x : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) :
    lineInc c n x = Pi.single 0 (levEquiv c n x) := rfl

theorem lineInc_injective (c : Coef l) (n : ℕ) : Function.Injective (lineInc c n) :=
  fun x y h => (levEquiv c n).injective (by
    have h0 := congrFun h 0
    simpa [lineInc_apply] using h0)

variable [IsAlgClosure ℚ Ω]

theorem lineInc_equiv (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (B : ValuationSubring Ω)
    (hup : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (θ : Dec (F := ℚ) B →* c.Oˣ)
    (hθ : ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = mat W g 0 0) (g : Dec (F := ℚ) B)
    (x : UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) :
    lineInc c n (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ g x) =
      ((rhoS c n W hint S hN).comp (locHom (S : Set Pl) B)) g (lineInc c n x) := by
  have h1 : (θ g : c.O) = ⟨mat W g 0 0, hint g 0 0⟩ := Subtype.ext (hθ g)
  have h2 : matQ c n W hint g 1 0 = 0 := by
    rw [matQ_apply]
    have : (⟨mat W g 1 0, hint g 1 0⟩ : c.O) = 0 := Subtype.ext (hup g g.2)
    rw [this, map_zero]
  show lineInc c n (((θ g : c.Oˣ) : c.O) • x) = matQ c n W hint g *ᵥ lineInc c n x
  rw [lineInc_apply, lineInc_apply, levEquiv_smul, h1]
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, matQ_apply]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h2]

theorem card_ordCond_le (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (hcont : Continuous W) (B : ValuationSubring Ω)
    (hup : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) (θ : Dec (F := ℚ) B →* c.Oˣ)
    (hθ : ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = mat W g 0 0)
    [Finite (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ))] :
    Nat.card (ordCond c n W hint S hN B) ≤
      Nat.card (H1 (Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ)) := by
  set τ := Formalism.GaloisCohomology.scalRep (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) θ with hτ
  set σ := (rhoS c n W hint S hN).comp (locHom (S : Set Pl) B) with hσ
  have hσa : ∀ (g : Dec (F := ℚ) B) (y : Mn c n), σ g y = matQ c n W hint g *ᵥ y := fun _ _ => rfl
  have heq := lineInc_equiv c n W hint S hN B hup θ hθ
  set Φ := UpperTheory.V.X.h1MapOfAdditive τ σ (lineInc c n) heq with hΦ
  have hsub : (ordCond c n W hint S hN B : Set (H1 σ)) ⊆ Set.range Φ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨x, hx⟩ := (mem_ordZ _).1 (Submodule.mem_comap.1 hz)

    set m : Mn c n := Pi.single 1 x with hm
    have hbc : Continuous fun g : Dec (F := ℚ) B => σ g m - m := by
      have hc : ∀ i j, Continuous fun g : Dec (F := ℚ) B => matQ c n W hint g i j := fun i j =>
        (continuous_matQ_apply c n W hint hcont i j).comp continuous_subtype_val
      refine continuous_pi fun i => ?_
      simp only [hσa, Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      exact (((hc i 0).mul continuous_const).add ((hc i 1).mul continuous_const)).sub continuous_const
    let bZ : Z1 σ := ⟨fun g => σ g m - m, hbc, fun g h => by
      simp only [map_mul, Module.End.mul_apply, map_sub]
      abel⟩
    have hbB : bZ ∈ (B1 σ).comap (Z1 σ).subtype := (mem_coboundaries1 σ _).2 ⟨m, fun g => rfl⟩
    set zb : Z1 σ := z - bZ with hzb
    have hzb1 : ∀ g, zb.1 g 1 = 0 := by
      intro g
      show z.1 g 1 - (σ g m - m) 1 = 0
      have hx' : z.1 g 1 = matQ c n W hint g 1 1 * x - x := hx g
      rw [hσa, hx']
      have hm0 : m 0 = 0 := rfl
      have hm1 : m 1 = x := rfl
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hm0, hm1]
      ring
    have hzbι : ∀ g, zb.1 g = lineInc c n ((levEquiv c n).symm (zb.1 g 0)) := by
      intro g
      rw [lineInc_apply, AddEquiv.apply_symm_apply]
      ext i
      fin_cases i
      · simp
      · simp [hzb1 g]
    let w : Dec (F := ℚ) B → UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n) := fun g => (levEquiv c n).symm (zb.1 g 0)
    have hw : w ∈ Z1 τ := by
      refine ⟨(continuous_of_discreteTopology (f := fun y : Mn c n => (levEquiv c n).symm (y 0))).comp zb.2.1,
        fun g h => lineInc_injective c n ?_⟩
      rw [map_add, heq, ← hzbι, ← hzbι, ← hzbι]
      exact zb.2.2 g h
    refine ⟨Submodule.Quotient.mk ⟨w, hw⟩, ?_⟩
    rw [hΦ, UpperTheory.V.X.h1MapOfAdditive_mk]
    have e1 : UpperTheory.V.X.cocycleMapOfEquivariant τ σ (lineInc c n) heq ⟨w, hw⟩ = zb :=
      Subtype.ext (funext fun g => (hzbι g).symm)
    rw [e1, hzb, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hbB, sub_zero]
    rfl
  calc Nat.card (ordCond c n W hint S hN B) = Nat.card (ordCond c n W hint S hN B : Set (H1 σ)) := rfl
    _ ≤ Nat.card (Set.range Φ) := Nat.card_mono (Set.finite_range Φ) hsub
    _ ≤ Nat.card (H1 τ) := Finite.card_range_le Φ

end GlobalTheory.Ord2.GwIneq.CardOrd

namespace GlobalTheory.Ord2.GwIneq.CardOrd

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_theta (c : Coef l) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hcont : Continuous W)
    (hdet : dt W ^ 2 = 1) (B : ValuationSubring Ω) (hup : ∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) :
    ∃ θ : Dec (F := ℚ) B →* c.Oˣ, Continuous (fun g => ((θ g : c.Oˣ) : c.O)) ∧
      ∀ g, (((θ g : c.Oˣ) : c.O) : Qbar l) = mat W g 0 0 := by
  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hcont
  refine GlobalTheory.LocChar.unit_of_integral l Ω c B (fun s => mat W s 0 0)
    (fun s => eps l s * (mat W s 1 1 * (mat W s).det)) ((hm.matrix_elem 0 0).continuousOn) ?_ ?_
  · intro s hs
    have hdetO : (mat W s).det ∈ c.O := by
      rw [Matrix.det_fin_two]
      exact c.O.sub_mem (c.O.mul_mem (hint s 0 0) (hint s 1 1)) (c.O.mul_mem (hint s 0 1) (hint s 1 0))
    refine ⟨hint s 0 0, c.O.mul_mem (CupCob.eps_mem c s) (c.O.mul_mem (hint s 1 1) hdetO), ?_⟩
    have hd : (mat W s).det = mat W s 0 0 * mat W s 1 1 := by
      rw [Matrix.det_fin_two, hup s hs, mul_zero, sub_zero]
    have h2 := CupCob.det_sq W hdet s
    calc mat W s 0 0 * (eps l s * (mat W s 1 1 * (mat W s).det))
        = eps l s * ((mat W s 0 0 * mat W s 1 1) * (mat W s).det) := by ring
      _ = eps l s * (mat W s).det ^ 2 := by rw [← hd]; ring
      _ = eps l s := by rw [h2, mul_one]
  · intro s _ t ht
    show mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0
    simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have := hup t ht
    simp only [mat] at this
    rw [this, mul_zero, add_zero]

variable [IsAlgClosure ℚ Ω]

theorem exists_ne_one (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) :
    ∃ s ∈ Dec (F := ℚ) A, mat W s 0 0 ≠ 1 := by
  set D := Dec (F := ℚ) A with hDdef
  have hup : ∀ s ∈ D, mat W s 1 0 = 0 := hW.upper
  have h00 : ∀ s t, t ∈ D → mat W (s * t) 0 0 = mat W s 0 0 * mat W t 0 0 := by
    intro s t ht
    simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have := hup t ht
    simp only [mat] at this
    rw [this, mul_zero, add_zero]
  have hv : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hA, hlv⟩ := hW.atL
    simpa using (hA _).2 hlv
  obtain ⟨u0, hu0⟩ := GrOfKill.exists_unit_one_add l
  obtain ⟨t, htI, htu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u0
  have heps : eps l t = ((1 + l : ℕ) : Qbar l) := by
    simp [eps, cycBar, htu, hu0]
  obtain ⟨m, hm1, hm⟩ := hW.wt
  have htD : t ∈ D := Ine_le_Dec A htI
  have hpow00 : ∀ s ∈ D, ∀ k : ℕ, mat W (s ^ k) 0 0 = mat W s 0 0 ^ k := by
    intro s hs k
    induction k with
    | zero => simp [mat]
    | succ k ih => rw [pow_succ, h00 _ _ hs, ih, pow_succ]
  refine ⟨t ^ m, D.pow_mem htD m, fun h => ?_⟩
  have hT : mat W (t ^ m) 0 0 = (((1 + l) ^ (e * m) : ℕ) : Qbar l) := by
    rw [hpow00 t htD, hm t htI, heps]; push_cast; ring
  rw [hT] at h
  have h1 : (1 + l) ^ (e * m) = 1 := by exact_mod_cast h
  have hl1 : 1 < 1 + l := by have := (Fact.out : l.Prime).two_le; omega
  have : 1 < (1 + l) ^ (e * m) :=
    Nat.one_lt_pow (Nat.mul_ne_zero (by have := hW.e_pos; omega) (by omega)) hl1
  omega

theorem card_ord : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W →
    ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1),
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ v : S, IsPlaceOver A v.1 →
      Nat.card (Lc c n W hint S hN A v) ≤ C * Nat.card (Qn c n) := by
  intro hL l _ Ω _ _ _ e S A W hW c hint hN
  obtain ⟨θ, hθc, hθ⟩ := exists_theta c W hint hW.cont hW.det2 A hW.upper
  have h1 : ∃ g, θ g ≠ 1 := by
    obtain ⟨s, hs, hne⟩ := exists_ne_one e S A W hW
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have := hθ ⟨s, hs⟩
    rw [h] at this
    exact this.symm
  have h2 : ∃ g, θ g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g := by
    obtain ⟨s, hs, hne⟩ := hW.ne
    refine ⟨⟨s, hs⟩, fun h => hne ?_⟩
    have := hθ ⟨s, hs⟩
    rw [h] at this
    exact this.symm
  obtain ⟨C, hC⟩ := GlobalTheory.LocChar.local_character_h1_bound hL.lf hL.lt hL.le l Ω c A hW.atL θ hθc h1 h2
  refine ⟨C, fun n hn v hv => ?_⟩
  obtain ⟨hfin, hcard⟩ := hC n hn
  have hAv : Av A S v = A := if_pos hv
  have hLc : Nat.card (Lc c n W hint S hN A v) = Nat.card (ordCond c n W hint S hN (Av A S v)) :=
    congrArg (fun p : Submodule _ _ => Nat.card p)
      (if_pos hv : Lc c n W hint S hN A v = ordCond c n W hint S hN (Av A S v))
  rw [hLc, hAv, ← card_lev]
  exact (card_ordCond_le c n W hint S hN hW.cont A hW.upper θ hθ).trans hcard

end GlobalTheory.Ord2.GwIneq.CardOrd
