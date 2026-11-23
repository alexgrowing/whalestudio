import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace GlobalTheory.Mem.Col2.Th

open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (emb : ι → H.E →+* ℂ)

abbrev Lt (N : ℕ) : Type := Submodule (𝓞 H.E) (Fin N → H.E)

abbrev VC (ι : Type) (N N' : ℕ) : Type := ι → Fin N' → Fin N → ℂ

def lamOf (cc : Ideal (𝓞 H.K)) (δ : ℂ) : AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * H.φ₀ (((c : H.K) : H.E))}

def IsDiscriminantTwelfthRootOfIdealLattice (cc : Ideal (𝓞 H.K)) (δ : ℂ) : Prop := δ ^ 12 = TaylorLogMetric.discr (lamOf H cc 1)

def IsTwoTorsionPointUnkilled (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt H.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt H.d : ℂ)) / 2) * t ∉ Λ

def stdL (N : ℕ) : Lt H N := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 H.E) H.E)

def homL {N N' : ℕ} (L : Lt H N) (L' : Lt H N') : Submodule (𝓞 H.E) (Matrix (Fin N') (Fin N) H.E) :=
  Submodule.span (𝓞 H.E) {A | ∀ x ∈ L, A.mulVec x ∈ L'}

def YYl {N N' : ℕ} (L : Lt H N) (L' : Lt H N') : Submodule (𝓞 H.E) (Matrix (Fin N') (Fin N) H.E) :=
  Submodule.span (𝓞 H.E) {B | ∃ a ∈ (H.AA0 : Submodule (𝓞 H.E) H.E), ∃ A ∈ homL H L L', B = a • A}

def La (Λ : AddSubgroup ℂ) {N N' : ℕ} (L : Lt H N) (L' : Lt H N') : AddSubgroup (VC ι N N') :=
  AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ A ∈ YYl H L L', z = w • (fun τ i j => emb τ (A i j) : VC ι N N')}

def Hf (Λ : AddSubgroup ℂ) {N N' : ℕ} (z w : VC ι N N') : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (TaylorLogMetric.area Λ : ℂ)

def al (Λ : AddSubgroup ℂ) {N N' : ℕ} (x : VC ι N N') : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt H.d / 2 * (Hf Λ x x).re))

def U (Λ : AddSubgroup ℂ) {N N' : ℕ} (x : VC ι N N') (G : VC ι N N' → ℂ) : VC ι N N' → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf Λ z x - (Real.pi : ℂ) * Hf Λ x x / 2)

def Iop (Λ : AddSubgroup ℂ) {N N' : ℕ} (La₁ La₂ : AddSubgroup (VC ι N N')) (G : VC ι N N' → ℂ) : VC ι N N' → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al H Λ ((Quotient.out q : La₂) : VC ι N N') * U Λ ((Quotient.out q : La₂) : VC ι N N') G z

def detId {N : ℕ} (L L' : Lt H N) : Submodule (𝓞 H.E) H.E :=
  Submodule.span (𝓞 H.E) {x | ∃ A : Matrix (Fin N) (Fin N) H.E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

def lamMM (Λ : AddSubgroup ℂ) : AddSubgroup (ι → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ Λ, ∃ a ∈ H.AA0, z = fun τ => w * emb τ a}

def mmM (M : IntermediateField ℚ ℂ) [NumberField M] : Submodule (𝓞 M) (ι → M) :=
  Submodule.span (𝓞 M) {v | ∃ a ∈ (H.AA0 : Submodule (𝓞 H.E) H.E), v = fun τ => TaylorLogMetric.liftM M (emb τ a)}

def ellT (M : IntermediateField ℚ ℂ) [NumberField M] (τ : ι) : Submodule (𝓞 M) M :=
  (mmM H emb M).comap (LinearMap.single (𝓞 M) (fun _ : ι => (M : Type)) τ)

def IsDgen (cD : ι → ℂ) : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, emb τ x ∈ M) ∧ ∀ τ, ∃ s : M, (s : ℂ) = cD τ ∧
    ellT H emb M τ = Submodule.span (𝓞 M) {s}

def SplitK (p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(H.d : ℤ)) p = 1

variable (ι) in

abbrev IsoK : Type := IsoKG H.K H.E H.conj ι

variable {H} in

def AtP (γ : IsoK H ι) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → H.E, (∀ a, x a ∈ H.AA0) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : H.K) * γ.g x w ∈ (algebraMap (𝓞 H.K) H.K).range) ∧
  ∀ v : Fin 4 × ι → H.K, (∀ w, v w ∈ (algebraMap (𝓞 H.K) H.K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : H.E) * γ.g.symm v a ∈ H.AA0

variable {H} in

def detRel (γ γ₀ : IsoK H ι) : H.K :=
  LinearMap.det ((γ₀.g.symm.trans γ.g : (Fin 4 × ι → H.K) ≃ₗ[H.K] _) : (Fin 4 × ι → H.K) →ₗ[H.K] (Fin 4 × ι → H.K))

variable {H} in

structure KapIn (γ₀ : IsoK H ι) where
  pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 H.K)
  pp_over : ∀ p, p.Prime → SplitK H p → ((p : ℕ) : 𝓞 H.K) ∈ (pp p).asIdeal
  pi : ℕ → 𝓞 H.K
  pi_gen : ∀ p, p.Prime → SplitK H p → (pp p).asIdeal ^ classNumber H.K = Ideal.span {pi p}
  gaP : ℕ → IsoK H ι
  gaP_at : ∀ p, p.Prime → SplitK H p → AtP (gaP p) p
  rt : ℕ → ℂ
  rt_pow : ∀ p, p.Prime → SplitK H p → rt p ^ (2 * classNumber H.K)
    = H.φ₀ (((pi p : 𝓞 H.K) : H.K) : H.E) / H.φ₀ (H.conj (((pi p : 𝓞 H.K) : H.K) : H.E))

variable {H} in

def KapIn.yP {γ₀ : IsoK H ι} (k : KapIn γ₀) (p : ℕ) : ℤ :=
  -WithZero.log ((k.pp p).valuation H.K (detRel (k.gaP p) γ₀))

variable {H} in

def KapIn.kappa {γ₀ : IsoK H ι} (k : KapIn γ₀) : ℂ :=
  ∏ᶠ p : {p : ℕ // p.Prime ∧ SplitK H p}, k.rt p ^ (-(k.yP p))

structure VacIn (cc : Ideal (𝓞 H.K)) (δ : ℂ) where
  L : PeriodPair
  lat : L.lattice.toAddSubgroup = lamOf H cc δ
  ω₀ : ℂ
  t0 : IsTwoTorsionPointUnkilled H (lamOf H cc δ) (ω₀ / 2)
  γ₀ : IsoK H ι
  gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ)
  gC_spec : ∀ x : Fin 4 → H.E, gC (fun w => emb w.2 (x w.1)) = fun w => H.φ₀ ((γ₀.g x w : H.K) : H.E)
  kc : KapIn γ₀

def chiFac (χ : Submodule (𝓞 H.E) H.E → ℂ) (N N' : ℕ) (L : Lt H N) (L' : Lt H N') : ℂ :=
  χ (detId H (stdL H N) L) ^ (((N' / 2 : ℕ) : ℤ)) * χ (detId H (stdL H N') L') ^ (-((N / 2 : ℕ) : ℤ))

def perAA (cc : Ideal (𝓞 H.K)) : Submodule (𝓞 H.E) H.E :=
  Submodule.span (𝓞 H.E) {r | ∃ c ∈ cc, ∃ t ∈ H.AA0, r = (((c : 𝓞 H.K) : H.K) : H.E) * t}

namespace VacIn

variable {H emb} {cc : Ideal (𝓞 H.K)} {δ : ℂ} (V : VacIn H emb cc δ)

def thMM : (ι → ℂ) → ℂ := thM V.L V.ω₀ (Real.sqrt H.d / 2) (lamMM H emb (lamOf H cc δ)) V.gC V.kc.kappa

def thZero (N N' : ℕ) : VC ι N N' → ℂ := tensPow V.thMM N N'

def thHalf (N N' : ℕ) (L : Lt H N) : VC ι N N' → ℂ :=
  Iop H (lamOf H cc δ) (La H emb (lamOf H cc δ) (stdL H N) (stdL H N')) (La H emb (lamOf H cc δ) L (stdL H N')) (V.thZero N N')

def thMoved (N N' : ℕ) (L : Lt H N) (L' : Lt H N') : VC ι N N' → ℂ :=
  Iop H (lamOf H cc δ) (La H emb (lamOf H cc δ) L (stdL H N')) (La H emb (lamOf H cc δ) L L') (V.thHalf N N' L)

def eNat (χ : Submodule (𝓞 H.E) H.E → ℂ) (N N' : ℕ) (L : Lt H N) (L' : Lt H N') : VC ι N N' → ℂ :=
  fun z => chiFac H χ N N' L L' * V.thMoved N N' L L' z

end VacIn

section Record

variable (D : D7)

theorem lamOf_rec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : lamOf D.host cc δ = TaylorLogMetric.lamOf D cc δ := rfl

theorem isDiscriminantTwelfthRoot_host_iff (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : IsDiscriminantTwelfthRootOfIdealLattice D.host cc δ ↔ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ := Iff.rfl

theorem stdL_rec (N : ℕ) : stdL D.host N = StandardLatticesGL3.stdL D N := rfl

theorem detId_rec {N : ℕ} (L L' : Lt D.host N) : detId D.host L L' = TaylorLogMetric.detId D L L' := rfl

theorem La_rec (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (L : Lt D.host N) (L' : Lt D.host N') :
    La D.host (TaylorLogMetric.embT D) (lamOf D.host cc δ) L L' = TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) L L' := rfl

theorem isDgen_rec (cD : D.what₂.Tau → ℂ) : IsDgen D.host (TaylorLogMetric.embT D) cD ↔ Formalism.L2.Ker.IsDgen D cD := Iff.rfl

theorem chiFac_rec (χ : TaylorLogMetric.IdE D → ℂ) (N N' : ℕ) (L : Lt D.host N) (L' : Lt D.host N') :
    chiFac D.host χ N N' L L' = Formalism.L2.Ker.Base.chiFac χ N N' L L' := rfl

variable {D} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def KapIn.toRec {γ₀ : IsoK D.host D.what₂.Tau} (k : KapIn γ₀) : KapChoice (D := D) γ₀ :=
  ⟨k.pp, k.pp_over, k.pi, k.pi_gen, k.gaP, k.gaP_at, k.rt, k.rt_pow⟩

def KapIn.ofRec {γ₀ : IsoK D.host D.what₂.Tau} (k : KapChoice (D := D) γ₀) : KapIn γ₀ :=
  ⟨k.pp, k.pp_over, k.pi, k.pi_gen, k.gaP, k.gaP_at, k.rt, k.rt_pow⟩

def VacIn.toRec (V : VacIn D.host (TaylorLogMetric.embT D) cc δ) : Formalism.L2.Ker.Base D cc δ :=
  ⟨V.L, V.lat, V.ω₀, V.t0, V.γ₀, V.gC, V.gC_spec, V.kc.toRec⟩

def VacIn.ofRec (B : Formalism.L2.Ker.Base D cc δ) : VacIn D.host (TaylorLogMetric.embT D) cc δ :=
  ⟨B.L, B.lat, B.ω₀, B.t0, B.γ₀, B.gC, B.gC_spec, KapIn.ofRec B.kc⟩

theorem VacIn.toRec_ofRec (B : Formalism.L2.Ker.Base D cc δ) : (VacIn.ofRec B).toRec = B := rfl

theorem VacIn.ofRec_toRec (V : VacIn D.host (TaylorLogMetric.embT D) cc δ) : VacIn.ofRec V.toRec = V := rfl

theorem VacIn.thMM_rec (V : VacIn D.host (TaylorLogMetric.embT D) cc δ) : V.thMM = V.toRec.thMM := rfl

theorem VacIn.eNat_rec (V : VacIn D.host (TaylorLogMetric.embT D) cc δ) (χ : TaylorLogMetric.IdE D → ℂ) : V.eNat χ = V.toRec.eNat χ := rfl

end Record

example (Λ : AddSubgroup ℂ) {N N' : ℕ} (c : ℂ) (z w : VC ι N N') : Hf Λ (c • z) w = c * Hf Λ z w := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

example (Λ : AddSubgroup ℂ) {N N' : ℕ} (G : VC ι N N' → ℂ) : Iop H Λ ⊥ ⊥ G = G := by
  funext z
  have h0 : ∀ q : (⊥ : AddSubgroup (VC ι N N')) ⧸ (⊥ : AddSubgroup (VC ι N N')).addSubgroupOf ⊥,
      ((Quotient.out q : (⊥ : AddSubgroup (VC ι N N'))) : VC ι N N') = 0 := fun q => AddSubgroup.mem_bot.1 (Quotient.out q).2
  have hU : Unique ((⊥ : AddSubgroup (VC ι N N')) ⧸ (⊥ : AddSubgroup (VC ι N N')).addSubgroupOf ⊥) :=
    ⟨⟨QuotientAddGroup.mk 0⟩, fun q => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      rw [Subsingleton.elim x 0]
      rfl⟩
  simp only [Iop, h0, finsum_unique]
  simp [al, U, Hf]

theorem perAA_top : perAA H ⊤ = (H.AA0 : Submodule (𝓞 H.E) H.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨c, -, t, ht, rfl⟩
    exact (H.AA0 : Submodule (𝓞 H.E) H.E).smul_mem (algebraMap (𝓞 H.K) (𝓞 H.E) c) ht
  · intro t ht
    exact Submodule.subset_span ⟨1, trivial, t, ht, by simp⟩

end GlobalTheory.Mem.Col2.Th

end
