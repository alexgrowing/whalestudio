import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt

noncomputable section

namespace GlobalTheory.UnitaryIdemCut

section Gen

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

def cutM (b : A) (hb : b * b = b) : Matrix n n A →* Matrix n n A where
  toFun M := b • M + (1 - b) • 1
  map_one' := by rw [← add_smul]; simp
  map_mul' M N := by
    have h1 : b * (1 - b) = 0 := by linear_combination -hb
    have h2 : (1 - b) * b = 0 := by linear_combination -hb
    have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
    simp only [add_mul, mul_add, smul_mul_smul_comm, hb, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one]

def cutGL (b : A) (hb : b * b = b) : GL n A →* GL n A := Units.map (cutM b hb)

theorem cutGL_val (b : A) (hb : b * b = b) (g : GL n A) :
    (cutGL b hb g).val = b • g.val + (1 - b) • 1 := rfl

theorem map_cut (φ : A →+* B) (b : A) (M : Matrix n n A) :
    (b • M + (1 - b) • (1 : Matrix n n A)).map φ = φ b • M.map φ + (1 - φ b) • (1 : Matrix n n B) := by
  ext i j
  by_cases h : i = j <;> simp [h]

theorem bc_cutGL (φ : A →+* B) (b : A) (hb : b * b = b) (b' : B) (hb' : b' * b' = b') (e : φ b = b')
    (g : GL n A) : bc φ (cutGL b hb g) = cutGL b' hb' (bc φ g) := by
  subst e
  exact Units.ext (map_cut φ b g.val)

theorem bc_cutGL_eq_one (φ : A →+* B) (b : A) (hb : b * b = b) {g : GL n A} (hg : bc φ g = 1) :
    bc φ (cutGL b hb g) = 1 := by
  rw [bc_cutGL φ b hb _ (by rw [← map_mul, hb]) rfl, hg, map_one]

theorem cutGL_conj (b : A) (hb : b * b = b) (β g : GL n A) :
    cutGL b hb (β * g * β⁻¹) = β * cutGL b hb g * β⁻¹ := by
  apply Units.ext
  simp only [cutGL_val, Units.val_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

theorem cutGL_mem_UJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) {g : GL n A}
    (hg : g ∈ UJ σ J) : cutGL b hb g ∈ UJ σ J := by
  have hg' : cT σ g.val * J * g.val = J := hg
  show cT σ (b • g.val + (1 - b) • 1) * J * (b • g.val + (1 - b) • 1) = J
  have e : cT σ (b • g.val + (1 - b) • (1 : Matrix n n A)) = b • cT σ g.val + (1 - b) • 1 := by
    unfold cT
    rw [map_cut, hσ, transpose_add, transpose_smul, transpose_smul, transpose_one]
  have h1 : b * (1 - b) = 0 := by linear_combination -hb
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  rw [e]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, hb, h1, h2, h3, zero_smul, add_zero,
    zero_add, mul_one, one_mul, hg']
  rw [← add_smul]; simp

def cutUJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) : UJ σ J →* UJ σ J :=
  ((cutGL b hb).comp (UJ σ J).subtype).codRestrict _ fun g => cutGL_mem_UJ σ J b hb hσ g.2

end Gen

section Ad

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.DIV
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem idem_mem_intAd (a : FiniteAdeleRing (𝓞 F) F) (ha : a * a = a) : a ∈ intAd F := by
  intro v
  have h : a v * a v = a v := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) ha
  rcases eq_or_ne (a v) 0 with h0 | h0
  · rw [h0]; exact zero_mem _
  · rw [mul_left_cancel₀ h0 (h.trans (mul_one _).symm)]; exact one_mem _

theorem cutGL_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : E ⊗[F] Formalism.L2.Herm.Af F) (hb : b * b = b)
    (hi : b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hg : g ∈ St β) :
    cutGL b hb g ∈ St β := by
  obtain ⟨y, rfl⟩ := hg
  refine ⟨cutGL (⟨b, hi⟩ : Formalism.L2.Herm.intAf F E) (Subtype.ext hb) y, ?_⟩
  show β * intGL F E n _ * β⁻¹ = cutGL b hb (β * intGL F E n y * β⁻¹)
  rw [cutGL_conj]
  unfold intGL
  rw [bc_cutGL _ _ _ b hb rfl]

theorem bc_cutGL_mem_St {A : Type} [CommRing A] (φ : A →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : A) (hb : b * b = b)
    (hi : φ b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) A} (hg : bc φ g ∈ St β) :
    bc φ (cutGL b hb g) ∈ St β := by
  have hb' : φ b * φ b = φ b := by rw [← map_mul, hb]
  rw [bc_cutGL φ b hb _ hb' rfl]
  exact cutGL_mem_St β _ hb' hi hg

end Ad

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sigR_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem exists_cutHA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (r : R)
    (hb : algebraMap R (R ⊗[F] E) r * algebraMap R (R ⊗[F] E) r = algebraMap R (R ⊗[F] E) r) :
    ∃ κ : HA R σ J →* HA R σ J, ∀ g, HA.mat R σ J (κ g) = cutGL _ hb (HA.mat R σ J g) :=
  ⟨cutUJ (sigR R σ) (JR R J) _ hb (sigR_algebraMap R σ r), fun _ => rfl⟩

theorem mem_GfC_iff {D : D7} (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ Formalism.UG.bc (infPart D) (matHom V g) = 1 := Iff.rfl

theorem finE_eq {D : D7} (V : HSp D) (g : GA D V) : finE V g = Formalism.UG.bc (toEAf D) (matHom V g) :=
  Units.ext (finE_val V g)

theorem exists_cut : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (ε : AF D.host.F), ε * ε = ε → ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ (Stab V β g → Stab V β (κ g)) := by
  intro D V β ε hε
  have hb : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε = algebraMap (AF D.host.F) (AE D) ε := by
    rw [← map_mul, hε]
  obtain ⟨κ, hκ⟩ := exists_cutHA (AF D.host.F) D.sp.cm.sig V.gram ε hb
  have hκ' : ∀ g, matHom V (κ g) = cutGL _ hb (matHom V g) := hκ
  refine ⟨κ, fun g => ⟨congrArg Units.val (hκ' g), fun h => ⟨?_, ?_⟩⟩⟩
  · have h1 := (mem_GfC_iff V g).1 h.1
    rw [mem_GfC_iff, hκ']
    exact bc_cutGL_eq_one (infPart D) _ hb h1
  · have h1 := h.2
    rw [finE_eq] at h1
    have hi : toEAf D (algebraMap (AF D.host.F) (AE D) ε) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨sndA D.host.F ε, idem_mem_intAd _ (by rw [← map_mul, hε])⟩, rfl⟩)
    rw [finE_eq, hκ']
    exact bc_cutGL_mem_St (toEAf D) β _ hb hi h1

end GlobalTheory.UnitaryIdemCut

end
