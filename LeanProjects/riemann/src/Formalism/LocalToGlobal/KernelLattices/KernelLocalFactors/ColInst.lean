import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Host Formalism.FrobeniusOrbits

section Fin

variable {E : Type} [Field E] [NumberField E]

theorem exists_pow_loc (P : HeightOneSpectrum (𝓞 E)) (k : ℕ) (hk : 0 < k) :
    ∃ e : ℕ, ∀ j ∈ P.asIdeal ^ e, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∃ r : 𝓞 E, t * j = (k : 𝓞 E) * r := by
  have hk0 : Ideal.span {(k : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk.ne'
  obtain ⟨e, B, hB, hkB⟩ := WfDvdMonoid.max_power_factor hk0 P.irreducible
  refine ⟨e, fun j hj => ?_⟩
  have hB' : ¬ B ≤ P.asIdeal := fun h => hB (Ideal.dvd_iff_le.2 h)
  obtain ⟨t, htB, htP⟩ := SetLike.not_le_iff_exists.1 hB'
  refine ⟨t, htP, ?_⟩
  have h1 : t * j ∈ Ideal.span {(k : 𝓞 E)} := by
    rw [hkB, mul_comm t j]
    exact Ideal.mul_mem_mul hj htB
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
  exact ⟨r, by rw [← hr, mul_comm]⟩

theorem semilocal_reps {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (M₀ M : Submodule (𝓞 E) H) (hfg : M₀.FG) (h1 : M₀ ≤ M)
    (h2 : ∀ x ∈ M, ∀ P ∈ S, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ M₀) (k : ℕ) (hk : 0 < k)
    (h3 : ∀ x ∈ M, ∀ j : 𝓞 E, (∀ P ∈ S, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∃ r : 𝓞 E, t * j = (k : 𝓞 E) * r) →
      ∃ y ∈ M, (k : 𝓞 E) • y = j • x) :
    ∃ F : Set H, F.Finite ∧ ∀ x ∈ M, ∃ f ∈ F, ∃ y ∈ M, x = f + (k : 𝓞 E) • y := by
  classical

  have ha : ∀ x ∈ M, ∃ m ∈ M₀, ∃ y ∈ M, x = m + (k : 𝓞 E) • y := by
    intro x hx
    choose e he using fun P : HeightOneSpectrum (𝓞 E) => exists_pow_loc P k hk
    let I : Ideal (𝓞 E) := M₀.comap (LinearMap.toSpanSingleton (𝓞 E) H x)
    have hI : ∀ s : 𝓞 E, s ∈ I ↔ s • x ∈ M₀ := fun s => by
      simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
    have hco : IsCoprime I (∏ P ∈ S, P.asIdeal ^ e P) := by
      refine IsCoprime.prod_right fun P hP => IsCoprime.pow_right ?_
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      obtain ⟨s, hs, hsx⟩ := h2 x hx P hP
      have h4 : P.asIdeal = I ⊔ P.asIdeal := P.isMaximal.eq_of_le hne le_sup_right
      exact hs (h4 ▸ (Ideal.mem_sup_left ((hI s).2 hsx)))
    obtain ⟨s, hs, j, hj, hsj⟩ := Ideal.isCoprime_iff_exists.1 hco
    have hj' : ∀ P ∈ S, j ∈ P.asIdeal ^ e P := fun P hP =>
      (Finset.inf_le hP : (S.inf fun P => P.asIdeal ^ e P) ≤ _) (Ideal.prod_le_inf hj)
    obtain ⟨y, hy, hky⟩ := h3 x hx j fun P hP => he P j (hj' P hP)
    refine ⟨s • x, (hI s).1 hs, y, hy, ?_⟩
    rw [hky, ← add_smul, hsj, one_smul]

  have : Module.Finite (𝓞 E) M₀ := Module.Finite.iff_fg.2 hfg
  have hk0 : Ideal.span {(k : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(k : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hk0
  have : Finite (↥M₀ ⧸ (Ideal.span {(k : 𝓞 E)} • (⊤ : Submodule (𝓞 E) ↥M₀))) :=
    Submodule.finite_quotient_smul _ Module.Finite.fg_top
  let Q := ↥M₀ ⧸ (Ideal.span {(k : 𝓞 E)} • (⊤ : Submodule (𝓞 E) ↥M₀))
  let rep : Q → H := fun z => ((Function.surjInv (Submodule.Quotient.mk_surjective _) z : ↥M₀) : H)
  refine ⟨Set.range rep, Set.finite_range rep, fun x hx => ?_⟩
  obtain ⟨m, hm, y, hy, rfl⟩ := ha x hx
  refine ⟨rep (Submodule.Quotient.mk ⟨m, hm⟩), ⟨_, rfl⟩, ?_⟩
  obtain ⟨r0, hrep, h5⟩ : ∃ r0 : ↥M₀, rep (Submodule.Quotient.mk ⟨m, hm⟩) = (r0 : H) ∧
      r0 - ⟨m, hm⟩ ∈ Ideal.span {(k : 𝓞 E)} • (⊤ : Submodule (𝓞 E) ↥M₀) :=
    ⟨_, rfl, (Submodule.Quotient.eq _).1 (Function.surjInv_eq _ _)⟩
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h5
  obtain ⟨w, -, hw⟩ := h5
  have h6 : rep (Submodule.Quotient.mk ⟨m, hm⟩) - m = (k : 𝓞 E) • (w : H) := by
    have h7 := congrArg (Subtype.val) hw
    rw [Submodule.coe_smul, AddSubgroupClass.coe_sub] at h7
    rw [hrep]
    exact h7.symm
  refine ⟨y - (w : H), M.sub_mem hy (h1 w.2), ?_⟩
  rw [smul_sub, ← h6]
  abel

theorem mem_mulLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (c : ℕ) (M : Submodule (𝓞 E) H) (w : H) :
    w ∈ mulLat c M ↔ ∃ y ∈ M, (c : 𝓞 E) • y = w := by
  unfold mulLat
  rw [Submodule.mem_map]
  rfl

theorem finite_quot_of_reps {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (M : Submodule (𝓞 E) H) (c k : ℕ) (F : Set H) (hF : F.Finite)
    (hFM : ∀ x ∈ M, ∃ f ∈ F, ∃ y ∈ M, x = f + (k : 𝓞 E) • y) :
    Finite (↥(mulLat c M) ⧸ (mulLat (c * k) M).comap (mulLat c M).subtype) := by
  have : Finite ↥(F ∩ (M : Set H)) := (hF.inter_of_left _).to_subtype
  let φ : ↥(F ∩ (M : Set H)) → (↥(mulLat c M) ⧸ (mulLat (c * k) M).comap (mulLat c M).subtype) := fun f =>
    Submodule.Quotient.mk ⟨(c : 𝓞 E) • (f : H), (mem_mulLat c M _).2 ⟨f, f.2.2, rfl⟩⟩
  refine Finite.of_surjective φ fun z => ?_
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨x, hx, rfl⟩ := (mem_mulLat c M w).1 hw
  obtain ⟨f, hf, y, hy, hxy⟩ := hFM x hx
  have hfM : f ∈ M := by
    have : f = x - (k : 𝓞 E) • y := by rw [hxy]; abel
    rw [this]
    exact M.sub_mem hx (M.smul_mem _ hy)
  refine ⟨⟨f, hf, hfM⟩, ?_⟩
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  show (c : 𝓞 E) • f - (c : 𝓞 E) • x ∈ mulLat (c * k) M
  refine (mem_mulLat _ M _).2 ⟨-y, M.neg_mem hy, ?_⟩
  rw [hxy, Nat.cast_mul, smul_add, smul_neg, mul_smul]
  abel

variable [StarRing E] {a b : ℕ}

def homG (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) : Submodule (𝓞 E) (HomE E a b) where
  carrier := {x | ∀ y ∈ N, x y ∈ N'}
  add_mem' := fun hx hx' y hy => add_mem (hx y hy) (hx' y hy)
  zero_mem' := fun _ _ => zero_mem _
  smul_mem' := fun r _ hx y hy => Submodule.smul_mem _ r (hx y hy)

theorem homG_fg (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : Submodule.IsLattice E N)
    (hN' : Submodule.IsLattice E N') : (homG N N').FG := by
  obtain ⟨G, hG⟩ := hN.fg
  have : Module.Finite (𝓞 E) ↥N' := Module.Finite.iff_fg.2 hN'.fg
  let ev : ↥(homG N N') →ₗ[𝓞 E] (↥G → ↥N') :=
    { toFun := fun x g => ⟨x.1 g.1, x.2 g.1 (hG ▸ Submodule.subset_span g.2)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro x x' h
    apply Subtype.ext
    have hspan : Submodule.span E (G : Set (Sp E a)) = ⊤ := by
      rw [eq_top_iff, ← hN.span_eq_top, Submodule.span_le, ← hG]
      exact fun y hy => Submodule.span_subset_span (𝓞 E) E _ hy
    refine LinearMap.ext_on hspan fun g hg => ?_
    exact congrArg Subtype.val (congrFun h ⟨g, hg⟩)
  have : Module.Finite (𝓞 E) ↥(homG N N') := Module.Finite.of_injective ev hinj
  exact Module.Finite.iff_fg.1 this

theorem homG_le (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) :
    homG N N' ≤ homAt S N N' := by
  intro x hx P _ y hy
  obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
  refine (mem_locP P N' _).2 ⟨s, hs, ?_⟩
  rw [← LinearMap.map_smul_of_tower]
  exact hx _ hsy

theorem homAt_clear (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG)
    (x : HomE E a b) (hx : x ∈ homAt S N N') (P : HeightOneSpectrum (𝓞 E)) (hP : P ∈ S) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ homG N N' := by
  classical
  obtain ⟨G, hG⟩ := hN
  have h1 : ∀ g : Sp E a, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ (g ∈ G → s • x g ∈ N') := by
    intro g
    by_cases hg : g ∈ G
    · obtain ⟨s, hs, h⟩ := (mem_locP P N' _).1 (hx P hP g (le_locP P N (hG ▸ Submodule.subset_span hg)))
      exact ⟨s, hs, fun _ => h⟩
    · exact ⟨1, one_notMem P, fun h => absurd h hg⟩
  choose s hs hsx using h1
  refine ⟨∏ g ∈ G, s g, fun h => ?_, ?_⟩
  · obtain ⟨g, _, hg⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 h
    exact hs g hg
  · intro y hy
    rw [← hG] at hy
    induction hy using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s hg
      show (∏ g ∈ G, s g) • x g ∈ N'
      rw [hc, mul_comm, mul_smul]
      exact N'.smul_mem _ (hsx g hg)
    | zero => rw [map_zero]; exact N'.zero_mem
    | add y y' _ _ h h' => rw [map_add]; exact N'.add_mem h h'
    | smul r y _ h => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem _ h

theorem homAt_div (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (k : ℕ) (hk : 0 < k)
    (x : HomE E a b) (hx : x ∈ homAt S N N') (j : 𝓞 E)
    (hj : ∀ P ∈ S, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∃ r : 𝓞 E, t * j = (k : 𝓞 E) * r) :
    ∃ y ∈ homAt S N N', (k : 𝓞 E) • y = j • x := by
  have hk0 : (k : E) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨(((j : 𝓞 E) : E) / (k : E)) • x, ?_, ?_⟩
  · intro P hP n hn
    obtain ⟨t, ht, r, hr⟩ := hj P hP
    refine indexBasic_smul_locP P.asIdeal N' ht ?_
    have h1 : t • ((((j : 𝓞 E) : E) / (k : E)) • x) n = r • x n := by
      have h2 : ((t : 𝓞 E) : E) * ((j : 𝓞 E) : E) = (k : E) * ((r : 𝓞 E) : E) := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hr
      rw [LinearMap.smul_apply, ← algebraMap_smul E t, ← algebraMap_smul E r, smul_smul]
      congr 1
      show ((t : 𝓞 E) : E) * (((j : 𝓞 E) : E) / (k : E)) = ((r : 𝓞 E) : E)
      field_simp
      rw [h2, mul_comm]
    rw [h1]
    exact Submodule.smul_mem _ r (hx P hP n hn)
  · rw [← algebraMap_smul E (k : 𝓞 E), ← algebraMap_smul E j, smul_smul]
    congr 1
    show (((k : ℕ) : 𝓞 E) : E) * (((j : 𝓞 E) : E) / (k : E)) = ((j : 𝓞 E) : E)
    push_cast
    field_simp

theorem lattice_classes_finite_refinement (X : Fields) (a b : ℕ) (Sall : Finset (HeightOneSpectrum (𝓞 X.E))) : LatFin (X := X) a b Sall := by
  intro N N' c c' hN hN' _ hc'
  obtain ⟨F, hF, hFM⟩ := semilocal_reps Sall (homG N N') (homAt Sall N N') (homG_fg N N' hN.1 hN'.1) (homG_le Sall N N')
    (fun x hx P hP => homAt_clear Sall N N' hN.1.fg x hx P hP) c' hc' (fun x hx j hj => homAt_div Sall N N' c' hc' x hx j hj)
  exact finite_quot_of_reps _ c c' F hF hFM

end Fin

section Yb

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def semiLoc (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) (Sp E n) where
  carrier := {z | ∀ P ∈ S, z ∈ localization₂ P.asIdeal N}
  add_mem' := fun hx hx' P hP => add_mem (hx P hP) (hx' P hP)
  zero_mem' := fun _ _ => zero_mem _
  smul_mem' := fun r _ hx P hP => Submodule.smul_mem _ r (hx P hP)

theorem semiLoc_div (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) (k : ℕ) (hk : 0 < k)
    (x : Sp E n) (hx : x ∈ semiLoc S N) (j : 𝓞 E)
    (hj : ∀ P ∈ S, ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∃ r : 𝓞 E, t * j = (k : 𝓞 E) * r) :
    ∃ y ∈ semiLoc S N, (k : 𝓞 E) • y = j • x := by
  have hk0 : (k : E) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨(((j : 𝓞 E) : E) / (k : E)) • x, ?_, ?_⟩
  · intro P hP
    obtain ⟨t, ht, r, hr⟩ := hj P hP
    refine indexBasic_smul_locP P.asIdeal N ht ?_
    have h1 : t • ((((j : 𝓞 E) : E) / (k : E)) • x) = r • x := by
      have h2 : ((t : 𝓞 E) : E) * ((j : 𝓞 E) : E) = (k : E) * ((r : 𝓞 E) : E) := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hr
      rw [← algebraMap_smul E t, ← algebraMap_smul E r, smul_smul]
      congr 1
      show ((t : 𝓞 E) : E) * (((j : 𝓞 E) : E) / (k : E)) = ((r : 𝓞 E) : E)
      field_simp
      rw [h2, mul_comm]
    rw [h1]
    exact Submodule.smul_mem _ r (hx P hP)
  · rw [← algebraMap_smul E (k : 𝓞 E), ← algebraMap_smul E j, smul_smul]
    congr 1
    show (((k : ℕ) : 𝓞 E) : E) * (((j : 𝓞 E) : E) / (k : E)) = ((j : 𝓞 E) : E)
    push_cast
    field_simp

theorem natE_smul_mem (L : Submodule (𝓞 E) (Sp E n)) (d : ℕ) {z : Sp E n} (hz : z ∈ L) : (d : E) • z ∈ L := by
  have : (d : E) • z = (d : 𝓞 E) • z := by
    rw [← algebraMap_smul E (d : 𝓞 E) z, map_natCast]
  rw [this]
  exact L.smul_mem _ hz

theorem cosets_finite (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (i₁ i₂ : SB → ℕ) :
    {Y : Set (Sp E n) | ∃ y ∈ locLat SB N (fun P => -(i₁ P : ℤ)), Y = {z | z - y ∈ locLat SB N (fun P => (i₂ P : ℤ))}}.Finite := by
  classical
  set Q : ℕ := ∏ P : SB, Col.qOf P.1 ^ (i₁ P + i₂ P) with hQ
  have hQpos : 0 < Q := Finset.prod_pos fun P _ => pow_pos (qOf_pos P.1) _
  have hQ0 : (Q : E) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hq0 : ∀ P : SB, (Col.qOf P.1 : E) ≠ 0 := fun P => by exact_mod_cast (qOf_pos P.1).ne'
  have hd1 : ∀ P : SB, Col.qOf P.1 ^ i₁ P ∣ Q := fun P =>
    dvd_trans (pow_dvd_pow _ (Nat.le_add_right _ _)) (Finset.dvd_prod_of_mem (fun P : SB => Col.qOf P.1 ^ (i₁ P + i₂ P)) (Finset.mem_univ P))
  have hd2 : ∀ P : SB, Col.qOf P.1 ^ i₂ P ∣ Q := fun P =>
    dvd_trans (pow_dvd_pow _ (Nat.le_add_left _ _)) (Finset.dvd_prod_of_mem (fun P : SB => Col.qOf P.1 ^ (i₁ P + i₂ P)) (Finset.mem_univ P))
  obtain ⟨F, hF, hFM⟩ := semilocal_reps SB N (semiLoc SB N) hN (fun z hz P _ => le_locP P N hz)
    (fun x hx P hP => (mem_locP P N x).1 (hx P hP)) (Q * Q) (Nat.mul_pos hQpos hQpos)
    (fun x hx j hj => semiLoc_div SB N (Q * Q) (Nat.mul_pos hQpos hQpos) x hx j hj)
  refine (hF.image fun f => {z : Sp E n | z - (Q : E)⁻¹ • f ∈ locLat SB N (fun P => (i₂ P : ℤ))}).subset ?_
  rintro Y ⟨y, hy, rfl⟩
  have h1 : (Q : E) • y ∈ semiLoc SB N := by
    intro P hP
    obtain ⟨d, hd⟩ := hd1 ⟨P, hP⟩
    have h2 := (mem_locLat SB N _ y).1 hy ⟨P, hP⟩
    have h3 : (Q : E) • y = (d : E) • ((((Col.qOf P : ℕ) : E) ^ (-(i₁ ⟨P, hP⟩ : ℤ)))⁻¹ • y) := by
      rw [smul_smul, hd, zpow_neg, inv_inv, zpow_natCast]
      push_cast
      rw [mul_comm]
    rw [h3]
    exact natE_smul_mem _ d h2
  obtain ⟨f, hf, w, hw, hfw⟩ := hFM _ h1
  refine ⟨f, hf, ?_⟩
  have h4 : y - (Q : E)⁻¹ • f ∈ locLat SB N (fun P => (i₂ P : ℤ)) := by
    have h5 : y - (Q : E)⁻¹ • f = (Q : E) • w := by
      have h6 : y = (Q : E)⁻¹ • ((Q : E) • y) := by rw [smul_smul, inv_mul_cancel₀ hQ0, one_smul]
      rw [h6, hfw, smul_add, add_sub_cancel_left, ← algebraMap_smul E ((Q * Q : ℕ) : 𝓞 E) w, smul_smul, map_natCast]
      congr 1
      push_cast
      field_simp
    rw [h5, mem_locLat]
    intro P
    obtain ⟨d, hd⟩ := hd2 P
    have h7 : (((Col.qOf P.1 : ℕ) : E) ^ ((i₂ P : ℕ) : ℤ))⁻¹ • ((Q : E) • w) = (d : E) • w := by
      rw [smul_smul, hd, zpow_natCast]
      congr 1
      push_cast
      have := pow_ne_zero (i₂ P) (hq0 P)
      field_simp
    rw [h7]
    exact natE_smul_mem _ d (hw P.1 P.2)
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    have : z - y = (z - (Q : E)⁻¹ • f) - (y - (Q : E)⁻¹ • f) := by abel
    rw [this]
    exact Submodule.sub_mem _ h h4
  · intro h
    have : z - (Q : E)⁻¹ • f = (z - y) + (y - (Q : E)⁻¹ • f) := by abel
    rw [this]
    exact Submodule.add_mem _ h h4

end Yb

section Yb2

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem ybSet_finite {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (hN : N.FG) : (ybSet sel mu cst N).Finite := by
  classical
  have h := cosets_finite (rowSG Pr sel mu) N hN (fun P => if P.1 ∈ Pr.vGs then 1 else cst.M) (fun P => if P.1 ∈ Pr.vGs then 0 else cst.M)
  convert h using 1
  unfold ybSet
  have e1 : (fun P : rowSG Pr sel mu => if P.1 ∈ Pr.vGs then (-1 : ℤ) else -(cst.M : ℤ)) =
      fun P => -(((if P.1 ∈ Pr.vGs then 1 else cst.M : ℕ) : ℕ) : ℤ) := by
    funext P; split_ifs <;> simp
  have e2 : (fun P : rowSG Pr sel mu => if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)) =
      fun P => (((if P.1 ∈ Pr.vGs then 0 else cst.M : ℕ) : ℕ) : ℤ) := by
    funext P; split_ifs <;> simp
  rw [e1, e2]

theorem coupling_index_set_finite (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) : YbHyp (R := R) sel mu cst L u m2 b :=
  ⟨fun p => ybSet_finite sel mu cst _ p.deco.2.lat.fg⟩

end Yb2

section Inst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem muqTie_of_allG (h : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) : MuqTie Ch sel mu cst :=
  fun _ _ P hP => absurd (h P) hP

theorem stepHyp_of {a b : ℕ} {Sall : Finset (HeightOneSpectrum (𝓞 X.E))} {D : ℕ} (hD : 0 < D) (h : A.AnaStep a b Sall D) : A.StepHyp a b Sall D :=
  stepHyp_of_la A a b Sall D hD h.1 (lattice_classes_finite_refinement X a b Sall) h.2.1 h.2.2

theorem chTh_ok_amb (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst) (h : ThHyp W Ch sel mu cst A u m2) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2) :=
  chTh_ok W Ch sel mu cst A u m2 hm hT hq (fun i hi => stepHyp_of A (modulus_pos sel mu cst u hT) (h.1 i hi))
    (stepHyp_of A (modulus_pos sel mu cst u hT) h.2.1) h.2.2.1 h.2.2.2

theorem kerEquivC_of (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : KerHypOn W Ch sel mu cst L A u m2 b hY P) : KerEquivC W Ch sel mu cst L A u m2 b hY P :=
  ⟨h.1, cp1Equiv_of_on W Ch sel mu cst L _ b hY h.2.1, cp2Equiv_of_on W Ch sel mu cst L _ b hY P h.2.2⟩

end Inst

section SeamLat

open Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X)

def Seam.vec {n : ℕ} (x : Sp X.E n) : Fin n → D.host.E := fun i => s.iE (x i)

theorem Seam.int_iff (z : X.E) : s.iE z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ z ∈ (algebraMap (𝓞 X.E) X.E).range := by
  have h1 : ∀ w : D.host.E, w ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ↔ IsIntegral ℤ w := fun w =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 D.host.E)).symm
  have h2 : ∀ w : X.E, w ∈ (algebraMap (𝓞 X.E) X.E).range ↔ IsIntegral ℤ w := fun w =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 X.E)).symm
  rw [h1, h2]
  constructor
  · intro h
    have := map_isIntegral_int s.iE.symm.toRingHom h
    simpa using this
  · intro h
    exact map_isIntegral_int s.iE.toRingHom h

theorem Seam.vec_add {n : ℕ} (x y : Sp X.E n) : s.vec (x + y) = s.vec x + s.vec y := by
  funext i
  simp [Seam.vec]

theorem Seam.vec_smulE {n : ℕ} (c : X.E) (x : Sp X.E n) : s.vec (c • x) = s.iE c • s.vec x := by
  funext i
  simp [Seam.vec]

theorem Seam.vec_smulO {n : ℕ} (r : 𝓞 X.E) (r' : 𝓞 D.host.E) (h : s.iE (r : X.E) = (r' : D.host.E)) (x : Sp X.E n) : s.vec (r • x) = r' • s.vec x := by
  funext i
  show s.iE ((r • x) i) = (r' • s.vec x) i
  rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
  show s.iE (r : X.E) * _ = (r' : D.host.E) * _
  rw [h]
  rfl

theorem Seam.vec_span {n : ℕ} (T : Set (Sp X.E n)) {x : Sp X.E n} (hx : x ∈ Submodule.span (𝓞 X.E) T) :
    s.vec x ∈ Submodule.span (𝓞 D.host.E) (s.vec '' T) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero =>
    have : s.vec (0 : Sp X.E n) = 0 := by funext i; simp [Seam.vec]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [s.vec_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr'⟩ := (s.int_iff (r : X.E)).2 ⟨r, rfl⟩
    rw [s.vec_smulO r r' hr'.symm]
    exact Submodule.smul_mem _ _ hx

theorem Seam.vec_spanE {n : ℕ} (T : Set (Sp X.E n)) {x : Sp X.E n} (hx : x ∈ Submodule.span X.E T) :
    s.vec x ∈ Submodule.span D.host.E (s.vec '' T) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
  | zero =>
    have : s.vec (0 : Sp X.E n) = 0 := by funext i; simp [Seam.vec]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [s.vec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [s.vec_smulE]; exact Submodule.smul_mem _ _ hx

theorem Seam.vec_surj {n : ℕ} (y : Fin n → D.host.E) : s.vec (fun i => s.iE.symm (y i) : Sp X.E n) = y := by
  funext i
  simp [Seam.vec]

theorem Seam.mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) : y ∈ s.lat N ↔ ∃ x ∈ N, s.vec x = y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y h => exact h
    | zero => exact ⟨0, N.zero_mem, by funext i; simp [Seam.vec]⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨x', hx', rfl⟩ := hy'
      exact ⟨x + x', N.add_mem hx hx', s.vec_add x x'⟩
    | smul r y _ hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨r₀, hr₀⟩ := (s.int_iff (s.iE.symm (r : D.host.E))).1 ⟨r, by simp⟩
      refine ⟨r₀ • x, N.smul_mem _ hx, s.vec_smulO r₀ r ?_ x⟩
      show s.iE (algebraMap (𝓞 X.E) X.E r₀) = _
      rw [hr₀]
      simp
  · rintro ⟨x, hx, rfl⟩
    exact Submodule.subset_span ⟨x, hx, rfl⟩

theorem Seam.stdH_vec (hok : s.Ok) {n : ℕ} (x y : Sp X.E n) :
    (letI := D.host.cmStar; stdH D.host.E n (s.vec x) (s.vec y)) = s.iE (hStd X.E n x y) := by
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SD.stdH_eq]
  show _ = s.iE (∑ i, star (x i) * y i)
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hok.2]
  rfl

theorem Seam.sd_lat (hok : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (letI := D.host.cmStar; IsSDLat D.host.E n (s.lat N)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := hN.1.fg
    have h : s.lat N = Submodule.span (𝓞 D.host.E) (s.vec '' (S : Set (Sp X.E n))) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        exact s.vec_span _ (by rw [hS]; exact hx)
      · refine Submodule.span_mono (Set.image_mono ?_)
        rw [← hS]
        exact Submodule.subset_span
    rw [h]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · rw [eq_top_iff]
    intro y _
    have h1 : (fun i => s.iE.symm (y i) : Sp X.E n) ∈ Submodule.span X.E (N : Set (Sp X.E n)) := by
      rw [hN.1.span_eq_top]; trivial
    have h2 := s.vec_spanE _ h1
    rw [s.vec_surj] at h2
    exact Submodule.span_mono (fun z hz => Submodule.subset_span hz) h2
  · intro y
    constructor
    · intro hy x hx
      obtain ⟨y₀, hy₀, rfl⟩ := (s.mem_lat N y).1 hy
      obtain ⟨x₀, hx₀, rfl⟩ := (s.mem_lat N x).1 hx
      rw [s.stdH_vec hok, s.int_iff]
      have h1 : y₀ ∈ dual (hStd X.E n) N := by rw [hN.2]; exact hy₀
      exact Submodule.mem_one.1 ((mem_dual N y₀).1 h1 x₀ hx₀)
    · intro h
      refine (s.mem_lat N y).2 ⟨fun i => s.iE.symm (y i), ?_, s.vec_surj y⟩
      have hd : IsUnimodular (hStd X.E n) N := hN.2
      unfold IsUnimodular at hd
      rw [← hd, mem_dual]
      intro x₀ hx₀
      have h1 := h (s.vec x₀) ((s.mem_lat N _).2 ⟨x₀, hx₀, rfl⟩)
      rw [← s.vec_surj y, s.stdH_vec hok, s.int_iff] at h1
      exact Submodule.mem_one.2 h1

theorem Seam.admissible_of_selfDual_lattices (hok : s.Ok) {a b : ℕ} (ha : Even a) (hb : Even b) {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}
    (hN : IsSdLat N) (hN' : IsSdLat N') : TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') :=
  ⟨ha, hb, s.sd_lat hok hN, s.sd_lat hok hN'⟩

end SeamLat

section InstN

open Formalism.MainNotions

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (u : Pr.Word) (m2 : ℕ)

theorem lawTies_of_ok (hL : L.Ok Ch sel mu cst G m2) (hW : W.Ok)
    (hH : ∃ eta : Formalism.L2.Host.HChar X.E, Ch.Tied G.σ₀ (fun j τ => (W.row τ).e j) G.mu0 eta) : LawTies W Ch sel mu cst G :=
  ⟨muqTie_of_ok Ch sel mu cst L hL, muqTieG_of_ok Ch sel mu cst L hL, hH, hW.hc_row⟩

end InstN

section Tab

theorem mem_divLat {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (c : ℕ) (M : Submodule (𝓞 E) H) (w : H) :
    w ∈ divLat c M ↔ (c : 𝓞 E) • w ∈ M := Iff.rfl

theorem finite_div_quot {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H] [Module E H] [IsScalarTower (𝓞 E) E H]
    (M : Submodule (𝓞 E) H) (cA cB : ℕ) (hA : 0 < cA) (F : Set H) (hF : F.Finite)
    (hFM : ∀ x ∈ M, ∃ f ∈ F, ∃ y ∈ M, x = f + ((cA * cB : ℕ) : 𝓞 E) • y) :
    Finite (↥(divLat cA M) ⧸ (mulLat cB M).comap (divLat cA M).subtype) := by
  have hA0 : (cA : E) ≠ 0 := by exact_mod_cast hA.ne'
  have hcast : ∀ z : H, (cA : 𝓞 E) • ((cA : E)⁻¹ • z) = z := fun z => by
    rw [← algebraMap_smul E (cA : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hA0, one_smul]
  have : Finite ↥(F ∩ (M : Set H)) := (hF.inter_of_left _).to_subtype
  let φ : ↥(F ∩ (M : Set H)) → (↥(divLat cA M) ⧸ (mulLat cB M).comap (divLat cA M).subtype) := fun f =>
    Submodule.Quotient.mk ⟨(cA : E)⁻¹ • (f : H), (mem_divLat cA M _).2 (by rw [hcast]; exact f.2.2)⟩
  refine Finite.of_surjective φ fun z => ?_
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨f, hf, y, hy, hxy⟩ := hFM _ ((mem_divLat cA M x).1 hx)
  have hfM : f ∈ M := by
    have : f = (cA : 𝓞 E) • x - ((cA * cB : ℕ) : 𝓞 E) • y := by rw [hxy]; abel
    rw [this]
    exact M.sub_mem ((mem_divLat cA M x).1 hx) (M.smul_mem _ hy)
  refine ⟨⟨f, hf, hfM⟩, ?_⟩
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  show (cA : E)⁻¹ • f - x ∈ mulLat cB M
  refine (mem_mulLat _ M _).2 ⟨-y, M.neg_mem hy, ?_⟩
  have h1 : x = (cA : E)⁻¹ • ((cA : 𝓞 E) • x) := by
    rw [← algebraMap_smul E (cA : 𝓞 E), map_natCast, smul_smul, inv_mul_cancel₀ hA0, one_smul]
  rw [h1, hxy, smul_add, Nat.cast_mul, mul_smul, ← algebraMap_smul E (cA : 𝓞 E) ((cB : 𝓞 E) • y), map_natCast, smul_smul,
    inv_mul_cancel₀ hA0, one_smul, smul_neg]
  abel

theorem kerFin {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} (Sall : Finset (HeightOneSpectrum (𝓞 E)))
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (hN : IsSdLat N) (hN' : IsSdLat N') (cA cB : ℕ) (hA : 0 < cA) (hB : 0 < cB) :
    Finite (↥(divLat cA (homAt Sall N N')) ⧸ (mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype) := by
  obtain ⟨F, hF, hFM⟩ := semilocal_reps Sall (homG N N') (homAt Sall N N') (homG_fg N N' hN.1 hN'.1) (homG_le Sall N N')
    (fun x hx P hP => homAt_clear Sall N N' hN.1.fg x hx P hP) (cA * cB) (Nat.mul_pos hA hB)
    (fun x hx j hj => homAt_div Sall N N' (cA * cB) (Nat.mul_pos hA hB) x hx j hj)
  exact finite_div_quot _ cA cB hA F hF hFM

theorem jetLin_smul {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (c : K) (J : (DVar ι a b →₀ ℕ) → K) :
    jetLin (fun m => c * J m) = c • jetLin J := by
  apply (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext
  intro m
  rw [LinearMap.smul_apply]
  simp only [coe_basisMonomials, jetLin_monomial, one_mul, smul_monomial, smul_eq_mul]

theorem jetOp_smul {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (c : K)
    (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) : jetOp lam lam' (fun m => c * J m) n = c • jetOp lam lam' J n := by
  unfold jetOp jetMap
  rw [jetLin_smul]
  ext P
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E)))

theorem kerOf_tab (cA cB : ℕ) (hA : 0 < cA) (hB : 0 < cB) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (mI : SB → X.E → X.K) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB) (hN : IsSdLat N) (hN' : IsSdLat N')
    (Ξ : HomE X.E a b → X.K) :
    kerOf (thDistC A Sall SB (cA * cB) sel mU mI lam lam' n) Sall cA cB N fr N' fr' Ξ =
      (muInvDet sel SB mU mI N fr * (muInvDet sel SB mU mI N' fr')⁻¹) • jetOp lam lam' (A.tabK Sall cA cB N N' Ξ) n := by
  rw [kerOf_thDistC]
  have := kerFin Sall N N' hN hN' cA cB hA hB
  let _ := Fintype.ofFinite (↥(divLat cA (homAt Sall N N')) ⧸ (mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype)
  have hJ : A.tabK Sall cA cB N N' Ξ = fun m => ∑ z : ↥(divLat cA (homAt Sall N N')) ⧸ (mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype,
      Ξ ((Function.surjInv (Submodule.Quotient.mk_surjective ((mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype)) z :
        ↥(divLat cA (homAt Sall N N'))) : HomE X.E a b) *
      A.jetK Sall N N' cB ((Function.surjInv (Submodule.Quotient.mk_surjective ((mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype)) z :
        ↥(divLat cA (homAt Sall N N'))) : HomE X.E a b) m := by
    funext m
    unfold Amb.tabK latSum
    rw [finsum_eq_sum_of_fintype]
  unfold latSum
  rw [finsum_eq_sum_of_fintype, hJ, jetOp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [jetOp_smul, smul_comm]

end Tab

section Ne

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem cAof_pos : 0 < cAof sel mu cst := pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _

theorem cBof_pos (hT : 0 < Pr.T u) : 0 < cBof sel mu cst u := Nat.mul_pos hT (pow_pos (Finset.prod_pos fun P _ => qOf_pos P.1) _)

end Ne

section Zero

theorem jetOp_zero {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) :
    jetOp lam lam' (fun _ => (0 : K)) n = 0 := by
  have h := jetOp_smul lam lam' (0 : K) (fun _ => (0 : K)) n
  simp only [zero_mul, zero_smul] at h
  exact h

variable {X : Fields} (A : Amb X) {a b : ℕ}

variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)

end Zero

section Scal

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem exists_unit_pow (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (r : 𝓞 E) (hr : r ≠ 0) :
    ∃ k : ℕ, IntAt P ((r : E) / (q : E) ^ k) ∧ IntAt P ((r : E) / (q : E) ^ k)⁻¹ := by
  have hq0 : (q : E) ≠ 0 := by
    intro h
    apply hu
    have : ((q : ℕ) : 𝓞 E) = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [map_natCast, h, map_zero]
    rw [this]
    exact zero_mem _
  obtain ⟨B, hB⟩ := (Ideal.dvd_span_singleton.2 hq : P.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 E)})
  have hBP : ¬ B ≤ P.asIdeal := by
    intro h
    obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 h
    apply hu
    rw [← Ideal.dvd_span_singleton, hB, hC, sq, ← mul_assoc]
    exact Dvd.intro _ rfl
  obtain ⟨t, htB, htP⟩ := SetLike.not_le_iff_exists.1 hBP
  have hr0 : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨k, C, hC, hrC⟩ := WfDvdMonoid.max_power_factor hr0 P.irreducible
  have hrk : r ∈ P.asIdeal ^ k := by
    rw [← Ideal.dvd_span_singleton, hrC]
    exact Dvd.intro _ rfl
  have hrk1 : r ∉ P.asIdeal ^ (k + 1) := by
    intro h
    rw [← Ideal.dvd_span_singleton, hrC, pow_succ] at h
    exact hC ((mul_dvd_mul_iff_left (pow_ne_zero k P.ne_bot)).1 h)
  have htk : t ^ k ∉ P.asIdeal := fun h => htP (P.isPrime.mem_of_pow_mem k h)
  have h1 : t ^ k * r ∈ Ideal.span {((q : ℕ) : 𝓞 E) ^ k} := by
    rw [← Ideal.span_singleton_pow, hB, mul_pow, mul_comm (t ^ k) r]
    exact Ideal.mul_mem_mul hrk (Ideal.pow_mem_pow htB k)
  obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton'.1 h1
  have hr'P : r' ∉ P.asIdeal := by
    intro h
    have h2 : t ^ k * r ∈ P.asIdeal ^ (k + 1) := by
      rw [← hr', pow_succ, mul_comm r']
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hq k) h
    rcases Ideal.IsPrime.mul_mem_pow P.asIdeal h2 with h3 | h3
    · exact htk h3
    · exact hrk1 h3
  have hE : ((t ^ k : 𝓞 E) : E) * (r : E) = (r' : E) * (q : E) ^ k := by
    have := congrArg (fun z : 𝓞 E => (z : E)) hr'
    simp only [map_mul, map_pow, map_natCast] at this
    rw [← map_mul]
    simpa using this.symm
  have hrE : (r : E) ≠ 0 := by
    intro h
    exact hr (FaithfulSMul.algebraMap_injective (𝓞 E) E (h.trans (map_zero _).symm))
  have hr'E : (r' : E) ≠ 0 := by
    intro h
    apply hr'P
    have : r' = 0 := FaithfulSMul.algebraMap_injective (𝓞 E) E (h.trans (map_zero _).symm)
    rw [this]; exact zero_mem _
  have hqk : (q : E) ^ k ≠ 0 := pow_ne_zero k hq0
  refine ⟨k, ⟨r', t ^ k, htk, ?_⟩, ⟨t ^ k, r', hr'P, ?_⟩⟩
  · show ((t ^ k : 𝓞 E) : E) * ((r : E) / (q : E) ^ k) = (r' : E)
    rw [← mul_div_assoc, hE, mul_div_assoc, div_self hqk, mul_one]
  · show (r' : E) * ((r : E) / (q : E) ^ k)⁻¹ = ((t ^ k : 𝓞 E) : E)
    rw [inv_div, ← mul_div_assoc, ← hE, mul_div_assoc, div_self hrE, mul_one]

theorem exists_isUnit_div (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (a : E) (ha : a ≠ 0) :
    ∃ z : ℤ, IsUnit (redP P (a / (q : E) ^ z)) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply ha
    rw [map_zero, zero_div]
  obtain ⟨k, h1, h2⟩ := exists_unit_pow P q hq hu r hr0
  obtain ⟨l, h3, h4⟩ := exists_unit_pow P q hq hu s hs0
  have hq0 : (q : E) ≠ 0 := by
    intro h
    apply hu
    have : ((q : ℕ) : 𝓞 E) = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [map_natCast, h, map_zero]
    rw [this]
    exact zero_mem _
  have hsE : (algebraMap (𝓞 E) E s) ≠ 0 := fun h => hs0 (FaithfulSMul.algebraMap_injective (𝓞 E) E (by rw [h, map_zero]))
  have hrE : (algebraMap (𝓞 E) E r) ≠ 0 := fun h => hr0 (FaithfulSMul.algebraMap_injective (𝓞 E) E (by rw [h, map_zero]))
  refine ⟨(k : ℤ) - (l : ℤ), ?_⟩
  have e : algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s / (q : E) ^ ((k : ℤ) - (l : ℤ)) =
      (algebraMap (𝓞 E) E r / (q : E) ^ k) * (algebraMap (𝓞 E) E s / (q : E) ^ l)⁻¹ := by
    rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp
  rw [e]
  refine isUnit_reduction_of_integralAt_inv (h1.mul h4) ?_ (mul_ne_zero (div_ne_zero hrE (pow_ne_zero _ hq0)) (inv_ne_zero (div_ne_zero hsE (pow_ne_zero _ hq0))))
  rw [mul_inv, inv_inv]
  exact h2.mul h3

variable [StarRing E] {K : Type} [Field K]

end Scal

section Scal2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end Scal2

section JetNe

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

def specY (K : Type) [Field K] (ι : Type) (a b : ℕ) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K →ₐ[K] MvPolynomial (DVar ι a b) K :=
  aeval (Sum.elim (fun v => if v.2.1 = v.2.2 then 1 else 0) fun k => X k)

theorem specY_subD (hab : a ≤ b) :
    (specY K ι a b).comp (subD K ι a b) = rename fun v : ι × Fin a × Fin a => ((v.1, Fin.castLE hab v.2.2, v.2.1) : DVar ι a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  have hv : v.2.2.1 < b := lt_of_lt_of_le v.2.2.2 hab
  rw [AlgHom.comp_apply, rename_X]
  unfold subD specY
  rw [aeval_X, dif_pos hv, map_sum, Finset.sum_eq_single (⟨v.2.2.1, hv⟩ : Fin b)]
  · rw [map_mul, aeval_X, aeval_X]
    simp only [Sum.elim_inl, Sum.elim_inr, if_true, one_mul]
    rfl
  · intro β _ hβ
    rw [map_mul, aeval_X, aeval_X]
    simp only [Sum.elim_inl, if_neg hβ, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem subD_injective (hab : a ≤ b) : Function.Injective (subD K ι a b) := by
  have h1 : Function.Injective ((specY K ι a b).comp (subD K ι a b)) := by
    rw [specY_subD hab]
    refine rename_injective _ fun v w h => ?_
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Prod.ext h.2.2 (Fin.castLE_injective hab h.2.1))
  exact Function.Injective.of_comp (f := specY K ι a b) (by simpa using h1)

theorem frDet_ne_zero (τ : ι) : frDet K a τ ≠ 0 := by
  classical
  intro h
  have h1 := congrArg (eval fun v : ι × Fin a × Fin a => if v.2.1 = v.2.2 then (1 : K) else 0) h
  unfold frDet at h1
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (eval fun v : ι × Fin a × Fin a => if v.2.1 = v.2.2 then (1 : K) else 0).mapMatrix
      (Matrix.of fun α s : Fin a => (X (τ, α, s) : Pol K ι a)) = 1 := by
    ext α s
    simp [Matrix.one_apply]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem exists_jetLin_ne (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) (hQ : Q ≠ 0) : ∃ J : (DVar ι a b →₀ ℕ) → K, jetLin J Q ≠ 0 := by
  classical
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hQ
  refine ⟨fun m' => if m' = m.comapDomain Sum.inr Sum.inr_injective.injOn then 1 else 0, fun h => hm ?_⟩
  have h1 := congrArg (coeff (m.comapDomain Sum.inl Sum.inl_injective.injOn)) h
  rw [coeff_zero] at h1
  conv at h1 => lhs; rw [← support_sum_monomial_coeff Q, map_sum, coeff_sum]
  rw [Finset.sum_eq_single m] at h1
  · rw [jetLin_monomial, coeff_monomial, if_pos rfl, if_pos rfl, mul_one] at h1
    exact h1
  · intro m' _ hne
    rw [jetLin_monomial, coeff_monomial]
    by_cases hl : m'.comapDomain Sum.inl Sum.inl_injective.injOn = m.comapDomain Sum.inl Sum.inl_injective.injOn
    · rw [if_pos hl]
      have hr : m'.comapDomain Sum.inr Sum.inr_injective.injOn ≠ m.comapDomain Sum.inr Sum.inr_injective.injOn := by
        intro hr
        apply hne
        ext i
        rcases i with i | i
        · have := DFunLike.congr_fun hl i
          simpa [Finsupp.comapDomain_apply] using this
        · have := DFunLike.congr_fun hr i
          simpa [Finsupp.comapDomain_apply] using this
      rw [if_neg hr, mul_zero]
    · rw [if_neg hl]
  · intro hns
    rw [jetLin_monomial, notMem_support_iff.1 hns, zero_mul, monomial_zero, coeff_zero]

theorem exists_jetMap_ne (hab : a ≤ b) (n : ι → ℕ) (P : Pol K ι a) (hP : P ≠ 0) : ∃ J : (DVar ι a b →₀ ℕ) → K, jetMap J n P ≠ 0 := by
  have h1 : P * ∏ τ, frDet K a τ ^ n τ ≠ 0 :=
    mul_ne_zero hP (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (frDet_ne_zero τ))
  have h2 : subD K ι a b (P * ∏ τ, frDet K a τ ^ n τ) ≠ 0 := fun h => h1 (subD_injective hab (h.trans (map_zero _).symm))
  obtain ⟨J, hJ⟩ := exists_jetLin_ne _ h2
  exact ⟨J, hJ⟩

theorem exists_tabNe (hab : a ≤ b) (lam : ι → DomWeight a) (n : ι → ℕ) (hV : DIV.VV K lam ≠ ⊥) :
    ∃ J : (DVar ι a b →₀ ℕ) → K, TabNe lam n J := by
  obtain ⟨P, hP, hP0⟩ := (Submodule.ne_bot_iff _).1 hV
  obtain ⟨J, hJ⟩ := exists_jetMap_ne hab n P hP0
  exact ⟨J, P, hP, hJ⟩

end JetNe

section Wt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem nuW_last_nonneg (u : Pr.Word) (i : ℕ) (hi : i < R.m) (τ : X.Tau) : 0 ≤ (W.nuW u (i + 1) τ).detShift := by
  have hNpos : 0 < R.N i := R.N_pos i
  have h1 : (W.nuW u (i + 1) τ).detShift =
      (Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ + ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    show (shiftW (W.lamN u i τ) ⌊wG R ((RowPar.of (W.hc u τ)).eAt i) (i + 1)⌋).detShift = _
    unfold DomWeight.detShift RowPar.eAt
    rw [dif_pos hNpos, dif_pos hi]
    rfl
  have a1 : (((Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ : ℤ) : ℚ) = Examples₂.wtN (W.hc u τ) (R.N i - 1) := by
    rw [Examples₂.lamOf_eq (W.hc u τ) i hi.le, Examples₂.wtQ_eq_wtN]
  have hb : Examples₂.blkN R (R.N i) = i := by
    unfold Examples₂.blkN Ranks.N
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _)]
  have a2 : Examples₂.wtN (W.hc u τ) (R.N i) = -wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := by
    have gen : ∀ (c : ℕ) (hc : c < R.m), c = i → -wG R ((W.hc u τ).e ⟨c, hc⟩) (c + 1) = -wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := by
      rintro c hc rfl; rfl
    unfold Examples₂.wtN
    rw [dif_neg (by unfold Ranks.N; omega), dif_pos (by rw [hb]; exact hi)]
    exact gen _ _ hb
  have hlt : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  have hle : R.N (i + 1) ≤ R.N R.m := by
    unfold Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  have e : R.N i - 1 + 1 = R.N i := by omega
  have a3 : Examples₂.wtN (W.hc u τ) (R.N i) ≤ Examples₂.wtN (W.hc u τ) (R.N i - 1) := by
    have h := Examples₂.wtN_step (W.hc u τ) (R.N i - 1) (by rw [e]; exact lt_of_lt_of_le hlt hle)
    rwa [e] at h
  obtain ⟨z, hz⟩ := Examples₂.wtQ_int (W.hc u τ) (i + 1) hi ⟨R.N i, hlt⟩
  rw [Examples₂.wtQ_eq_wtN, a2] at hz
  have a4 : ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ = -z := by
    have : wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) = ((-z : ℤ) : ℚ) := by push_cast; linarith
    rw [this, Int.floor_intCast]
  rw [h1, a4]
  have : (z : ℚ) ≤ (((Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ : ℤ) : ℚ) := by
    rw [a1, ← hz, ← a2]; exact a3
  have h5 : z ≤ (Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ := by exact_mod_cast this
  omega

theorem nuLast_eq (u : Pr.Word) (i : ℕ) (hi : i < R.m) (τ : X.Tau) : ((nuLast W u i τ : ℕ) : ℤ) = (W.nuW u (i + 1) τ).detShift :=
  Int.toNat_of_nonneg (nuW_last_nonneg W u i hi τ)

theorem exists_tabNe_step (u : Pr.Word) (i : ℕ) : ∃ J : (DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → X.K, TabNe (W.lamTrue u i) (nuLast W u i) J :=
  exists_tabNe (by unfold Ranks.N; rw [Nat.succ_mul]; omega) _ _ (Submodule.nontrivial_iff_ne_bot.1 (VV_nontrivial X.K _))

end Wt

section InVV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem lamTrue_natW (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) (r : Fin (R.N (i + 1))) :
    (W.lamTrue u (i + 1) τ).natW r = extNu (R.N (i + 1)) (fun τ r => (W.lamTrue u i τ).natW r + nuLast W u i τ) τ r := by
  have hN : 0 < R.N i := R.N_pos i
  have hN' : 0 < R.N (i + 1) := R.N_pos (i + 1)
  have hlt : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [Nat.succ_mul]; omega
  have d' : (W.lamTrue u (i + 1) τ).detShift = (W.lamTrue u (i + 1) τ).w ⟨R.N (i + 1) - 1, by omega⟩ := by
    unfold DomWeight.detShift
    exact dif_pos hN'
  have d0 : (W.lamTrue u i τ).detShift = (W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ := by
    unfold DomWeight.detShift
    exact dif_pos hN
  have dn : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w (⟨R.N i - 1, by omega⟩ : Fin (R.N i)) := by
    unfold DomWeight.detShift
    exact dif_pos hN
  have e' := W.lamTrue_new u hi τ ⟨R.N (i + 1) - 1, by omega⟩ (by show ¬ R.N (i + 1) - 1 < R.N i; omega)
  have en := W.nuW_eq_true u hi τ ⟨R.N i - 1, by omega⟩
  have hl := nuLast_eq W u i hi τ
  unfold DomWeight.natW extNu
  by_cases h : r.1 < R.N i
  · rw [dif_pos h]
    have eo := W.lamTrue_old u hi τ r h
    have hanti : (W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ ≤ (W.lamTrue u i τ).w ⟨r.1, h⟩ :=
      (W.lamTrue u i τ).anti (by show r.1 ≤ R.N i - 1; omega)
    have key : (W.lamTrue u (i + 1) τ).w r - (W.lamTrue u (i + 1) τ).detShift =
        ((W.lamTrue u i τ).w ⟨r.1, h⟩ - (W.lamTrue u i τ).detShift) + (nuLast W u i τ : ℤ) := by
      have : (((W.lamTrue u (i + 1) τ).w r - (W.lamTrue u (i + 1) τ).detShift : ℤ) : ℚ) =
          ((((W.lamTrue u i τ).w ⟨r.1, h⟩ - (W.lamTrue u i τ).detShift) + (nuLast W u i τ : ℤ) : ℤ) : ℚ) := by
        rw [hl, dn, d', d0]
        push_cast
        rw [eo, e', en]
        ring
      exact_mod_cast this
    rw [key]
    show (_ : ℤ).toNat = ((W.lamTrue u i τ).w ⟨r.1, h⟩ - (W.lamTrue u i τ).detShift).toNat + nuLast W u i τ
    rw [d0]
    omega
  · rw [dif_neg h]
    have eo := W.lamTrue_new u hi τ r h
    have key : (W.lamTrue u (i + 1) τ).w r - (W.lamTrue u (i + 1) τ).detShift = 0 := by
      have : (((W.lamTrue u (i + 1) τ).w r - (W.lamTrue u (i + 1) τ).detShift : ℤ) : ℚ) = ((0 : ℤ) : ℚ) := by
        rw [d']
        push_cast
        rw [eo, e']
        ring
      exact_mod_cast this
    rw [key]
    rfl

theorem jet_in_weight_space_chain (u : Pr.Word) {i : ℕ} (hi : i < R.m) : JetInVVStep W u i (W.lamTrue u (i + 1)) :=
  jet_in_vv_of_weight X.K X.Tau (R.N i) (R.N (i + 1)) (by unfold Ranks.N; rw [Nat.succ_mul]; omega) _ _ _ (lamTrue_natW W u hi)

end InVV

section Crit

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

end Crit

section Unram

variable {X : Fields} {Pr : Primes X}

theorem xqQ_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : ((qOf w : ℕ) : 𝓞 E) ∈ w.asIdeal :=
  Ideal.absNorm_mem w.asIdeal

end Unram

section Red

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem xqIntAt_q : IntAt P (q : E) := by
  have := IntAt.coe P ((q : ℕ) : 𝓞 E)
  rwa [map_natCast] at this

theorem reduction_natCast_eq_zero₂ (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : redP P (q : E) = 0 := by
  have := reduction_coe P ((q : ℕ) : 𝓞 E)
  rw [map_natCast] at this
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hq

theorem xqIntAt_zero : IntAt P (0 : E) := by
  have := IntAt.coe P 0
  rwa [map_zero] at this

theorem xqIntAt_one : IntAt P (1 : E) := by
  have := IntAt.coe P 1
  rwa [map_one] at this

theorem reduction_zero₂ : redP P (0 : E) = 0 := by
  have := reduction_coe P 0
  rwa [map_zero, map_zero] at this

theorem reduction_one₃ : redP P (1 : E) = 1 := by
  have := reduction_coe P 1
  rwa [map_one, map_one] at this

theorem xqIntAt_intCast (z : ℤ) : IntAt P (z : E) := by
  have := IntAt.coe P (z : 𝓞 E)
  rwa [map_intCast] at this

theorem reduction_intCast (z : ℤ) : redP P (z : E) = (z : 𝓞 E ⧸ P.asIdeal) := by
  have := reduction_coe P (z : 𝓞 E)
  rwa [map_intCast, map_intCast] at this

theorem xqIntAt_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (xqIntAt_zero (P := P))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem reduction_sum₃ {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (reduction_zero₂ (P := P))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      reduction_add (h a (Finset.mem_insert_self a s)) (xqIntAt_sum s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem xqIntAt_prod {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (xqIntAt_one (P := P))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem reduction_prod {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∏ i ∈ s, f i) = ∏ i ∈ s, redP P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (reduction_one₃ (P := P))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      reduction_mul (h a (Finset.mem_insert_self a s)) (xqIntAt_prod s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem reduction_det₂ {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n E) (h : ∀ i j, IntAt P (N i j)) :
    redP P N.det = (N.map (redP P)).det := by
  rw [Matrix.det_apply', Matrix.det_apply', reduction_sum₃ _ _ fun σ _ => (xqIntAt_intCast _).mul (xqIntAt_prod _ _ fun i _ => h _ _)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [reduction_mul (xqIntAt_intCast _) (xqIntAt_prod _ _ fun i _ => h _ _), reduction_intCast,
    reduction_prod _ _ fun i _ => h _ _]
  rfl

end Red

section Scl

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem xqMem_stdAt {n : ℕ} (x : Sp E n) : x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

end Scl

section Cst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

variable {Ch}

end Cst

section Grp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

end Grp

section Lift

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

end Lift

section Mem

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

end Mem

section Mem2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

end Mem2

section Of

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem xqRedV_single {n : ℕ} (l : Fin n) : redV P (Pi.single l (1 : E)) = Pi.single l 1 := by
  funext i
  unfold redV
  by_cases h : i = l
  · rw [h, Pi.single_eq_same, Pi.single_eq_same, reduction_one₃]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, reduction_zero₂]

theorem xqSingle_mem {n : ℕ} (l : Fin n) : (Pi.single l (1 : E) : Sp E n) ∈ stdAt E n P := by
  rw [xqMem_stdAt]
  intro i
  by_cases h : i = l
  · rw [h, Pi.single_eq_same]; exact xqIntAt_one
  · rw [Pi.single_eq_of_ne h]; exact xqIntAt_zero

end Of

section Lev

variable {X : Fields} {Pr : Primes X} (Ch : Chars X Pr Examples₂.R0.m)

end Lev

section Chr

variable {X : Fields} {Pr : Primes X} (Ch : Chars X Pr Examples₂.R0.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)

end Chr

section Chr1

variable {X : Fields} {Pr : Primes X} (Ch : Chars X Pr Examples₂.R0.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)

end Chr1

section Phi

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

variable (P) in

def xqPhiCond (q : ℕ) (sharp : Bool) (k₀ r t j c n : ℕ) (M : ℕ → ℕ → E) : Prop :=
  (∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (M p p')) ∧
    (∀ p p', r + (j - 1) * t ≤ p → p < n + c → p' < r + (j - 1) * t → IntAt P (M p p' / (q : E))) ∧
    (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p' < p → p < r + (j - 1) * t → redP P (M p p') = 0) ∧
    (∀ p p', r ≤ p' → p' < r + (j - 1) * t → p < r + (j - 1) * t → (p' - r) / t < (p - r) / t → redP P (M p p') = 0) ∧
    (sharp = true → ∀ p, p < n + c → redP P (M p k₀) = if p = k₀ then 1 else 0)

end Phi

section XiLoc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem addChar_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A K) (a : A) : ψ a ≠ 0 := by
  intro h
  have h1 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

end XiLoc

section XiFr

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

def Cong1 {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n) : Prop :=
  (∀ x, f x ∈ stdAt E n P ↔ x ∈ stdAt E n P) ∧ ∀ x ∈ stdAt E n P, redV P (f x) = redV P x

theorem Cong1.symm {n : ℕ} {f : Sp E n ≃ₗ[E] Sp E n} (h : Cong1 P f) : Cong1 P f.symm := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have := h.1 (f.symm x)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · have h1 : f.symm x ∈ stdAt E n P := by
      have := h.1 (f.symm x)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.1 hx
    have := h.2 _ h1
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm

def xInc {n' : ℕ} (n : ℕ) (hn' : 0 < n') (a : E) : HomE E n' n :=
  LinearMap.pi fun l : Fin n => if h : l.1 < n' then LinearMap.proj ⟨l.1, h⟩
    else if l.1 = n - 1 then a • LinearMap.proj ⟨n' - 1, by omega⟩ else 0

theorem redV_single {n : ℕ} (i : Fin n) : redV P (Pi.single i (1 : E) : Sp E n) = Pi.single i 1 := xqRedV_single i

end XiFr

section XiGlob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

end XiGlob

section XiNum

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem notMem_of_coprime {q q' : ℕ} (h : Nat.Coprime q q') (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : ((q' : ℕ) : 𝓞 E) ∉ P.asIdeal := by
  intro hq'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  apply one_notMem P
  have h1 : ((a : ℤ) : 𝓞 E) * ((q : ℕ) : 𝓞 E) + ((b : ℤ) : 𝓞 E) * ((q' : ℕ) : 𝓞 E) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : 𝓞 E)) hab
  rw [← h1]
  exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hq) (P.asIdeal.mul_mem_left _ hq')

end XiNum

section XiOk

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

end XiOk

section Ref

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)

theorem qe_one : QE sel (1 : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime (1 : Chr X.F X.E X.K) = ∅ := by
    ext v
    simp [Qprime]
  unfold QE
  rw [dif_pos (by rw [h]; exact Set.finite_empty)]
  simp [h]

theorem bad_primes_over_g_trivial_tuple (P : rowSG Pr sel (mu0 X.F X.E X.K S)) : P.1 ∈ Pr.vGs := by
  classical
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · rw [show ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = 1 from rfl, qe_one] at h
    exact absurd h (Finset.notMem_empty P.1)

variable (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S)))
  (L : ChIdx X Pr R (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))) (A : Amb X) (u : Pr.Word)

end Ref

section Closed

variable (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hLL : cycQ nd2N ≤ LL) (Ch : Chars (nd2X LL hLL) (toyPrimes LL hLL) Examples₂.R0.m)
  (sel : HeightOneSpectrum (𝓞 (nd2X LL hLL).F) → HeightOneSpectrum (𝓞 (nd2X LL hLL).E)) (S : Set ℕ)
  (cst : LocCst (nd2X LL hLL) (rowSG (toyPrimes LL hLL) sel (mu0 (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S)))
  (L : ChIdx (nd2X LL hLL) (toyPrimes LL hLL) Examples₂.R0
    (QE sel ((mu0 (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S : Tup (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S) : Chr (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K)))
  (A : Amb (nd2X LL hLL)) (u : (toyPrimes LL hLL).Word)

end Closed

section NeCons

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

end NeCons

section TabSpec

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall : Finset (HeightOneSpectrum (𝓞 X.E)))

theorem derivAt0_const_mul {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (f : VCx ι a b → ℂ) (hf : ∀ k : ℕ, ContDiff ℂ k f) (m : DVar ι a b →₀ ℕ) :
    derivAt0 (fun w => c * f w) m = c * derivAt0 f m := by
  unfold derivAt0
  have h : (fun w => c * f w) = c • f := rfl
  rw [h, iteratedFDeriv_const_smul_apply (hf _).contDiffAt]
  rfl

theorem tabK_spec (cA cB : ℕ) (hA : 0 < cA) (hB : 0 < cB) (hsm : A.ESmooth a b) (hrat : A.JetsRat a b Sall (cA * cB))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (hN : IsSdLat N) (hN' : IsSdLat N') (Ξ : HomE X.E a b → X.K)
    (m : DVar X.Tau a b →₀ ℕ) :
    A.σ₀ (A.tabK Sall cA cB N N' Ξ m) = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thDat Sall cA cB N N' Ξ) m := by
  have := kerFin Sall N N' hN hN' cA cB hA hB
  let _ := Fintype.ofFinite (↥(divLat cA (homAt Sall N N')) ⧸ (mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype)
  set rep := fun z : ↥(divLat cA (homAt Sall N N')) ⧸ (mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype =>
    ((Function.surjInv (Submodule.Quotient.mk_surjective ((mulLat cB (homAt Sall N N')).comap (divLat cA (homAt Sall N N')).subtype)) z :
      ↥(divLat cA (homAt Sall N N'))) : HomE X.E a b) with hrep
  have hR : ∀ z, InRange Sall (cA * cB) cB N N' (rep z) := fun z =>
    ⟨hN, hN', hB, Dvd.intro_left _ rfl, divLat_mul_of cA cB _ (Subtype.coe_prop _)⟩
  have hs := indSmooth_of A a b Sall (cA * cB) hsm
  have h1 : A.thDat Sall cA cB N N' Ξ = fun w => ∑ z, A.σ₀ (Ξ (rep z)) * A.thInd Sall N N' cB (rep z) w := by
    funext w
    unfold Amb.thDat latSum
    rw [finsum_eq_sum_of_fintype]
  have h2 : derivAt0 (A.thDat Sall cA cB N N' Ξ) m = ∑ z, A.σ₀ (Ξ (rep z)) * derivAt0 (A.thInd Sall N N' cB (rep z)) m := by
    have h3 : derivAt0 (A.thDat Sall cA cB N N' Ξ) m = ∑ z, derivAt0 (fun w => A.σ₀ (Ξ (rep z)) * A.thInd Sall N N' cB (rep z) w) m := by
      unfold derivAt0
      rw [h1, iteratedFDeriv_sum (fun z _ => contDiff_const.mul (hs N N' cB (rep z) (hR z) _))]
      rw [Finset.sum_apply, _root_.sum_apply]
    rw [h3]
    exact Finset.sum_congr rfl fun z _ => derivAt0_const_mul _ _ (hs N N' cB (rep z) (hR z)) m
  have h4 : A.tabK Sall cA cB N N' Ξ m = ∑ z, Ξ (rep z) * A.jetK Sall N N' cB (rep z) m := by
    unfold Amb.tabK latSum
    rw [finsum_eq_sum_of_fintype]
  rw [h4, map_sum]
  unfold jetC
  rw [h2, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul, jetK_spec A Sall (cA * cB) hrat N N' cB (rep z) (hR z) m]
  unfold jetC
  ring

end TabSpec

section Xi2Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

end Xi2Loc

section Xi2Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end Xi2Glob

section Xi2T

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Xi2T

section Xi2Ok

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end Xi2Ok

section Joint

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

end Joint

end Formalism.L2.Ker
