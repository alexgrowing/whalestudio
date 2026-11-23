import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.BumpLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.WeilBound.ThetaLifts.LatticeBasics.MemLam
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LatAtVSelfDualK

set_option synthInstance.maxHeartbeats 200000

section
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA
namespace UpperTheory.SeparatedDualCondition
variable {F : Type} [Field F] [NumberField F]
private theorem exists_cond_pk (v : HeightOneSpectrum (𝓞 F)) (ψ₀ : AddChar (Fv F v) ℂ) (x₀ a : Fv F v) (hx₀ : ψ₀ x₀ ≠ 1)
    (ha0 : a ≠ 0) (ha : ∀ x ∈ v.adicCompletionIntegers F, ψ₀ (a * x) = 1) :
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ x, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) ↔
      c⁻¹ * x ∈ v.adicCompletionIntegers F := by
  classical
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ₀)
  let I : Ideal (v.adicCompletionIntegers F) :=
    { carrier := {o | ∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x₀ * o * y) = 1}
      add_mem' := by
        intro p q hp hq y hy
        have e : x₀ * ((p + q : v.adicCompletionIntegers F) : Fv F v) * y = x₀ * p * y + x₀ * q * y := by
          push_cast; ring
        rw [e, AddChar.map_add_eq_mul, hp y hy, hq y hy, one_mul]
      zero_mem' := by
        intro y _
        simp
      smul_mem' := by
        intro r p hp y hy
        have e : x₀ * ((r • p : v.adicCompletionIntegers F) : Fv F v) * y = x₀ * p * (r * y) := by
          simp only [smul_eq_mul]; push_cast; ring
        rw [e]
        exact hp _ (mul_mem r.2 hy) }
  have hI : ∀ o : v.adicCompletionIntegers F, o ∈ I ↔ ∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x₀ * o * y) = 1 :=
    fun _ => Iff.rfl
  have key : ∀ x, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x₀⁻¹ * x ∈ v.adicCompletionIntegers F := by
    intro x hx
    by_cases hx' : x = 0
    · subst hx'
      simp
    · refine ((v.adicCompletionIntegers F).mem_or_inv_mem (x₀⁻¹ * x)).resolve_right fun h => hx₀ ?_
      have := hx _ h
      have e : x * (x₀⁻¹ * x)⁻¹ = x₀ := by field_simp
      rwa [e] at this
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal I).principal
  have hbI : b ∈ I := by rw [hb]; exact Submodule.mem_span_singleton_self b
  have hmem : ∀ o, o ∈ I ↔ ∃ t : v.adicCompletionIntegers F, o = t * b := by
    intro o
    rw [hb, Submodule.mem_span_singleton]
    simp [eq_comm]
  have hb0 : (b : Fv F v) ≠ 0 := by
    intro h0
    have h0' : b = 0 := by exact_mod_cast h0
    have hk := key a ha
    have hin : (⟨_, hk⟩ : v.adicCompletionIntegers F) ∈ I := by
      rw [hI]
      intro y hy
      have := ha y hy
      simpa [hx0, mul_assoc, mul_inv_cancel_left₀] using this
    obtain ⟨t, ht⟩ := (hmem _).1 hin
    rw [h0', mul_zero] at ht
    have := congrArg Subtype.val ht
    simp [hx0, ha0] at this
  refine ⟨x₀ * b, mul_ne_zero hx0 hb0, fun x => ⟨fun hx => ?_, fun hx y hy => ?_⟩⟩
  · have hk := key x hx
    have hin : (⟨_, hk⟩ : v.adicCompletionIntegers F) ∈ I := by
      rw [hI]
      intro y hy
      have := hx y hy
      simpa [hx0, mul_assoc, mul_inv_cancel_left₀] using this
    obtain ⟨t, ht⟩ := (hmem _).1 hin
    have h2 : x₀⁻¹ * x = t * b := by simpa using congrArg Subtype.val ht
    have : (x₀ * b)⁻¹ * x = t := by
      rw [mul_inv, mul_comm x₀⁻¹, mul_assoc, h2]
      field_simp
    rw [this]
    exact t.2
  · have hh := (hI b).1 hbI (((x₀ * b)⁻¹ * x) * y) (mul_mem hx hy)
    have e : x₀ * b * ((x₀ * b)⁻¹ * x * y) = x * y := by
      field_simp
    rwa [e] at hh
private theorem sep_dual_pk (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψ₀ : AddChar (Fv F v) ℂ)
    (Λ L : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (hle : Λ ≤ L)
    (hdual : ∀ z, z ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1)
    (hst : ∀ a ∈ v.adicCompletionIntegers F, ∀ l ∈ L, a • l ∈ L)
    (c₀ : Fv F v) (hc₀ : c₀ ≠ 0)
    (hbd : ∀ l ∈ L, ∀ i, c₀ * l.1 i ∈ v.adicCompletionIntegers F ∧ c₀ * l.2 i ∈ v.adicCompletionIntegers F)
    (a : Fv F v) (ha0 : a ≠ 0) (ha : ∀ x ∈ v.adicCompletionIntegers F, ψ₀ (a * x) = 1)
    (y : (κ → Fv F v) × (κ → Fv F v)) (hy : y ∉ L) :
    ∃ u : (κ → Fv F v) × (κ → Fv F v), (∀ l ∈ L, ψ₀ (u.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ u.2) = 1) ∧
      ψ₀ (u.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ u.2) ≠ 1 := by
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ψ₀ x₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hy (hle ((hdual y).2 fun l _ => h _))
  obtain ⟨c, hc0, hc⟩ := exists_cond_pk v ψ₀ x₀ a hx₀ ha0 ha
  let O := v.adicCompletionIntegers F
  let L' : Submodule O ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := L
      add_mem' := fun h h' => L.add_mem h h'
      zero_mem' := L.zero_mem
      smul_mem' := fun t l hl => hst (t : Fv F v) t.2 l hl }
  let φ : ((κ → O) × (κ → O)) →ₗ[O] ((κ → Fv F v) × (κ → Fv F v)) :=
    { toFun := fun x => (fun i => c₀⁻¹ * (x.1 i : Fv F v), fun i => c₀⁻¹ * (x.2 i : Fv F v))
      map_add' := by intro x y; ext i <;> simp [mul_add]
      map_smul' := by intro t x; ext i <;> simp [Algebra.smul_def] <;> ring }
  have hle' : L' ≤ LinearMap.range φ := by
    intro l hl
    refine ⟨(fun i => ⟨c₀ * l.1 i, (hbd l hl i).1⟩, fun i => ⟨c₀ * l.2 i, (hbd l hl i).2⟩), ?_⟩
    ext i <;> simp [φ, hc₀]
  haveI : IsNoetherian O (LinearMap.range φ) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian O L' := isNoetherian_of_le hle'
  have hfg : L'.FG := Module.Finite.iff_fg.1 inferInstance
  have hspan : Submodule.span (Fv F v) (L' : Set ((κ → Fv F v) × (κ → Fv F v))) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨t, ht0, ht⟩ := GlobalTheory.LatBound.exists_mul_mem_integers v
      (fun s : κ ⊕ κ => Sum.elim (fun k => (c * c₀)⁻¹ * w.1 k) (fun k => (c * c₀)⁻¹ * w.2 k) s)
    have hw : t • w ∈ L := hle ((hdual _).2 fun l hl => by
      have hm : c⁻¹ * ((t • w).1 ⬝ᵥ l.2 - l.1 ⬝ᵥ (t • w).2) ∈ v.adicCompletionIntegers F := by
        rw [mul_sub]
        simp only [dotProduct, Finset.mul_sum]
        refine sub_mem (sum_mem fun k _ => ?_) (sum_mem fun k _ => ?_)
        · have := mul_mem (ht (Sum.inl k)) (hbd l (hle hl) k).2
          convert this using 1
          simp only [Sum.elim_inl, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          field_simp
        · have := mul_mem (ht (Sum.inr k)) (hbd l (hle hl) k).1
          convert this using 1
          simp only [Sum.elim_inr, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          field_simp
      have h1 := (hc _).2 hm 1 (one_mem _)
      rwa [mul_one] at h1)
    have e : w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hw)
  haveI : L'.IsLattice (Fv F v) := ⟨hfg, hspan⟩
  let ψ' : AddChar (Fv F v) ℂ := ψ₀.compAddMonoidHom (AddMonoidHom.mulLeft c)
  have hψ' : ∀ x, ψ' x = ψ₀ (c * x) := fun _ => rfl
  have hsep : ∀ x, (∀ y : O, ψ' (x * algebraMap O (Fv F v) y) = 1) ↔ x ∈ (algebraMap O (Fv F v)).range := by
    intro x
    have e : c⁻¹ * (c * x) = x := by field_simp
    have h := hc (c * x)
    rw [e] at h
    constructor
    · intro hx
      have hm := h.1 fun y hy => by
        have := hx ⟨y, hy⟩
        rw [hψ', ← mul_assoc] at this
        exact this
      exact ⟨⟨x, hm⟩, rfl⟩
    · rintro ⟨o, rfl⟩ y
      have := h.2 o.2 y y.2
      rw [hψ', ← mul_assoc]
      exact this
  obtain ⟨l, h1, h2⟩ := GlobalTheory.ThK.Dbl.Bmp.sep ψ' hsep L' hy
  let e : κ → κ → Fv F v := fun k j => if k = j then 1 else 0
  let A : (κ → Fv F v) →ₗ[Fv F v] Fv F v := l ∘ₗ LinearMap.inl _ _ _
  let Bm : (κ → Fv F v) →ₗ[Fv F v] Fv F v := l ∘ₗ LinearMap.inr _ _ _
  have hl : ∀ z, l z = ∑ k, z.1 k * A (e k) + ∑ k, z.2 k * Bm (e k) := by
    intro z
    have hz : z = (z.1, 0) + (0, z.2) := by simp
    have h1 := LinearMap.pi_apply_eq_sum_univ A z.1
    have h2 := LinearMap.pi_apply_eq_sum_univ Bm z.2
    simp only [smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
    conv_lhs => rw [hz, map_add]
    rfl
  have hu : ∀ z, ψ₀ ((fun k => c * Bm (e k)) ⬝ᵥ z.2 - z.1 ⬝ᵥ (fun k => -(c * A (e k)))) = ψ' (l z) := by
    intro z
    rw [hψ', hl, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    simp only [dotProduct]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  exact ⟨(fun k => c * Bm (e k), fun k => -(c * A (e k))), fun z hz => (hu z).trans (h1 z hz), fun h => h2 ((hu y).symm.trans h)⟩
open GlobalTheory.Idele in
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff) in
private theorem psi_triv_pk {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : Pl F) (x : Fv F v)
    (hx : x ∈ v.adicCompletionIntegers F) : GlobalTheory.LatVac.psiAt ψ v (1 * x) = 1 := by
  have h1 : (1 : Af F) ∈ adelicIdeal (codiff F) := by
    have h := (algebraMap_mem_adelicIdeal codiff_ne_zero (1 : F)).2
      ((one_le_codiff (F := F)) (FractionalIdeal.one_mem_one _))
    simpa using h
  have h2 := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) 1).1 h1 (singleFin v x) (by
    intro w
    by_cases h : w = v
    · subst h
      have e : (singleFin w x) w = x := evalV_singleFin_self w x
      rw [e]
      exact hx
    · have e : (singleFin v x) w = 0 := evalV_singleFin_ne h x
      rw [e]
      exact zero_mem _)
  rw [mul_one] at h2
  rw [one_mul]
  exact h2
private theorem locCo_smul'_pk {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : Pl F) (a : AF F) (w : W) :
    GlobalTheory.LatVac.locCo co v (a • w) = evFin F v a • GlobalTheory.LatVac.locCo co v w := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
  ext k <;> simp [smul_eq_mul, map_mul]
private theorem exists_at_pk {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : Pl F) (w : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ z : W, At (evFin F v) z ∧ GlobalTheory.LatVac.locCo co v z = w := by
  obtain ⟨p, hp⟩ : ∃ p : (κ → AF F) × (κ → AF F),
      p = (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) := ⟨_, rfl⟩
  refine ⟨co.e.symm p, fun u hu => ?_, ?_⟩
  · have hp0 : u • p = 0 := by
      subst hp
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
      · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
    rw [← map_smul, hp0, map_zero]
  · subst hp
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show evFin F v ((co.e (co.e.symm _)).1 k) = w.1 k
      rw [LinearEquiv.apply_symm_apply]
      exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
    · show evFin F v ((co.e (co.e.symm _)).2 k) = w.2 k
      rw [LinearEquiv.apply_symm_apply]
      exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)
private theorem at_inj_pk {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : Pl F) {z : W} (hz : At (evFin F v) z)
    (h0 : GlobalTheory.LatVac.locCo co v z = 0) : z = 0 := by
  have hz1 : GlobalTheory.LatVac.liftV v 1 • z = z := by
    have := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have he : co.e z = 0 := by
    rw [← hz1, map_smul]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have h : evFin F v ((co.e z).1 k) = 0 := congrFun (congrArg Prod.fst h0) k
      have := GlobalTheory.LatVac.at_liftV v 1 _ h
      simpa [smul_eq_mul, mul_comm] using this
    · have h : evFin F v ((co.e z).2 k) = 0 := congrFun (congrArg Prod.snd h0) k
      have := GlobalTheory.LatVac.at_liftV v 1 _ h
      simpa [smul_eq_mul, mul_comm] using this
  exact (map_eq_zero_iff co.e co.e.injective).1 he
private theorem common_bound_pk (v : Pl F) {c₁ c₂ : Fv F v} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    ∃ c : Fv F v, c ≠ 0 ∧ (∀ x, c₁ * x ∈ v.adicCompletionIntegers F → c * x ∈ v.adicCompletionIntegers F) ∧
      ∀ x, c₂ * x ∈ v.adicCompletionIntegers F → c * x ∈ v.adicCompletionIntegers F := by
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem (c₁⁻¹ * c₂) with h | h
  · refine ⟨c₂, h₂, fun x hx => ?_, fun x hx => hx⟩
    have := mul_mem h hx
    rwa [show c₁⁻¹ * c₂ * (c₁ * x) = c₂ * x by field_simp] at this
  · refine ⟨c₁, h₁, fun x hx => hx, fun x hx => ?_⟩
    have := mul_mem h hx
    rwa [show (c₁⁻¹ * c₂)⁻¹ * (c₂ * x) = c₁ * x by field_simp] at this
end UpperTheory.SeparatedDualCondition
open UpperTheory.SeparatedDualCondition in
theorem UpperTheory.exists_separating_of_not_mem_lattice_coset :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ v : Pl F, ∀ g ∈ UAt σ X (evFin F v), ∀ y : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) y → (∀ a ∈ latAtV X W v, ∀ b ∈ latAtV X W v, y ≠ a + mat g⁻¹ * b) → ∃ u ∈ latAtV X W v, mat g * u ∈ latAtV X W v ∧ B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u y) ≠ 1 := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW v g _ y hy hne
  classical
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have hO := (GlobalTheory.LatVac.latAtV_at_stable X W v).2
  have hself := _root_.GlobalTheory.LatSelfDualAll.latAtV_selfDual_k F E σ B n d X W r s r' s' hB hX hW v
  have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ (latAtV X W v) hat hself
  let S : AddSubgroup (Matrix (Fin n) (Fin d) (AE F E)) :=
    { carrier := {z | ∃ a ∈ latAtV X W v, ∃ b ∈ latAtV X W v, z = a + mat g⁻¹ * b}
      add_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by rw [Matrix.mul_add]; abel⟩
      zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
      neg_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact ⟨-a, neg_mem ha, -b, neg_mem hb, by rw [Matrix.mul_neg]; abel⟩ }
  have hmulat : ∀ (A : Matrix (Fin n) (Fin n) (AE F E)) (z : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) z →
      At (evFin F v) (A * z) := fun A z hz u hu => by
    rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]
  have hSat : ∀ z ∈ S, At (evFin F v) z := by
    rintro _ ⟨a, ha, b, hb, rfl⟩ u hu
    rw [smul_add, hat a ha u hu, hmulat _ b (hat b hb) u hu, add_zero]
  obtain ⟨c₁, hc₁0, hc₁⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat hW.lat
  obtain ⟨Mt, _, gm, hgm⟩ := GlobalTheory.LatParam.latAtV_param X W hX.lat hW.lat v
  obtain ⟨c₂, hc₂0, hc₂⟩ := GlobalTheory.LatBound.exists_mul_mem_integers v
    (fun t : Bool × Mt × (Fin n × Fin d) =>
      if t.1 then (GlobalTheory.LatVac.locCo M.co v (mat g⁻¹ * incM F (gm t.2.1))).1 t.2.2
      else (GlobalTheory.LatVac.locCo M.co v (mat g⁻¹ * incM F (gm t.2.1))).2 t.2.2)
  have hb2 : ∀ b ∈ latAtV X W v, ∀ i, c₂ * (GlobalTheory.LatVac.locCo M.co v (mat g⁻¹ * b)).1 i ∈ v.adicCompletionIntegers F ∧
      c₂ * (GlobalTheory.LatVac.locCo M.co v (mat g⁻¹ * b)).2 i ∈ v.adicCompletionIntegers F := by
    intro b hb i
    obtain ⟨a, rfl⟩ := (hgm b).1 hb
    simp only [Matrix.mul_sum, Matrix.mul_smul, map_sum, locCo_smul'_pk, GlobalTheory.EmbChart.evFin_atPlace, Prod.fst_sum, Prod.snd_sum,
      Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    constructor
    · refine sum_mem fun m _ => ?_
      rw [mul_left_comm]
      exact mul_mem (a m).2 (by simpa using hc₂ (true, m, i))
    · refine sum_mem fun m _ => ?_
      rw [mul_left_comm]
      exact mul_mem (a m).2 (by simpa using hc₂ (false, m, i))
  obtain ⟨c₀, hc₀, hb₁, hb₂⟩ := common_bound_pk v hc₁0 hc₂0
  have hbd : ∀ l ∈ S.map (GlobalTheory.LatVac.locCo M.co v), ∀ i, c₀ * l.1 i ∈ v.adicCompletionIntegers F ∧
      c₀ * l.2 i ∈ v.adicCompletionIntegers F := by
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩ i
    rw [map_add]
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add]
    exact ⟨add_mem (hb₁ _ (hc₁ a ha i).1) (hb₂ _ (hb2 b hb i).1), add_mem (hb₁ _ (hc₁ a ha i).2) (hb₂ _ (hb2 b hb i).2)⟩
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ S.map (GlobalTheory.LatVac.locCo M.co v),
      t • l ∈ S.map (GlobalTheory.LatVac.locCo M.co v) := by
    rintro t ht _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • (a + mat g⁻¹ * b), ⟨GlobalTheory.LatVac.liftV v t • a, hO t ht a ha,
      GlobalTheory.LatVac.liftV v t • b, hO t ht b hb, by rw [smul_add, Matrix.mul_smul]⟩, ?_⟩
    rw [locCo_smul'_pk, GlobalTheory.LatVac.evFin_liftV]
  have hle : (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v) ≤ S.map (GlobalTheory.LatVac.locCo M.co v) := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨γ, ⟨γ, hγ, 0, zero_mem _, by simp⟩, rfl⟩
  have hyL : GlobalTheory.LatVac.locCo M.co v y ∉ S.map (GlobalTheory.LatVac.locCo M.co v) := by
    rintro ⟨z, hzS, hz⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := id hzS
    refine hne a ha b hb (sub_eq_zero.1 (at_inj_pk M.co v (fun u hu => ?_) ?_)).symm
    · rw [smul_sub, hy u hu, hSat _ hzS u hu, sub_zero]
    · rw [map_sub, hz, sub_self]
  obtain ⟨w, hw1, hw2⟩ := sep_dual_pk v (GlobalTheory.LatVac.psiAt B.ψ v) _ _ hle hsd hst c₀ hc₀ hbd 1 one_ne_zero
    (psi_triv_pk hB.std v) _ hyL
  obtain ⟨z, hzat, rfl⟩ := exists_at_pk M.co v w
  have hform := fun γ => GlobalTheory.LatVac.DualLoc.psi_form M.co v B.ψ hzat γ
  have hgg : mat g * mat g⁻¹ = 1 := by
    show mat (g * g⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  refine ⟨z, (hself z hzat).2 fun γ hγ => ?_, (hself _ (hmulat _ z hzat)).2 fun γ hγ => ?_, ?_⟩
  · rw [hform]
    exact hw1 _ (hle ⟨γ, hγ, rfl⟩)
  · have e := GlobalTheory.SympInv.symp_act F E σ n d X W g 1 z (mat g⁻¹ * γ)
    have h1 : mat (1 : UA σ W.J) = 1 := rfl
    rw [h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, hgg, Matrix.one_mul] at e
    rw [e, hform]
    exact hw1 _ ⟨mat g⁻¹ * γ, ⟨0, zero_mem _, γ, hγ, by simp⟩, rfl⟩
  · rw [hform]
    exact hw2
end
