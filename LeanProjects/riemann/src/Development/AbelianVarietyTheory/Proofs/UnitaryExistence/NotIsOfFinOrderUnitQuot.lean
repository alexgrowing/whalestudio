import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeterminantCharacterIdentity
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClassScalarCompare

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity MvPolynomial
open scoped nonZeroDivisors Classical TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Poly

variable (c : Coeff l) {n : ℕ}

theorem mult_le (hn : Dw.p + Dw.q ≤ n) (σ : E →+* ℂ) : Dw.mult σ ≤ n := by
  unfold Datum.mult
  split_ifs <;> omega

def endCols (hn : Dw.p + Dw.q ≤ n) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) : Fin n :=
  if InPsi H σ then Fin.castLE (mult_le hn σ) i else (Fin.castLE (mult_le hn σ) i).rev

def revSign (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ℤˣ :=
  ∏ σ : E →+* ℂ, ∏ i : Fin (Dw.mult σ),
    (if InPsi H σ then 1 else Equiv.Perm.sign (Fin.revPerm (n := i.val + 1))) ^ aStep Dw a σ i.val

end Poly

section Adelic

variable {n : ℕ}

theorem star_diagE (x : E) : star (diagE E x) = diagE E (IsCMField.complexConj E x) := by
  show adConj E (1 ⊗ₜ x) = 1 ⊗ₜ _
  simp [adConj]

theorem map_conjTranspose (g : Matrix (Fin n) (Fin n) E) :
    g.conjTranspose.map (diagE E) = star (g.map (diagE E)) := by
  ext a b; exact (star_diagE _).symm

def toRat (g : Matrix (Fin n) (Fin n) E) (hg : g.conjTranspose * g = 1) : ratPts E n :=
  ⟨⟨g.map (diagE E), Matrix.mem_unitaryGroup_iff'.2 (by
      rw [← map_conjTranspose, ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero _) (map_one _)])⟩,
    fun a b => ⟨g a b, rfl⟩, fun a b => ⟨_, (star_diagE (g b a)).symm⟩⟩

def adTrace : AdE E →+ AdF E :=
  ((TensorProduct.rid (maximalRealSubfield E) (AdF E)).toLinearMap ∘ₗ
    LinearMap.lTensor (AdF E) (Algebra.trace (maximalRealSubfield E) E)).toAddMonoidHom

end Adelic

section Conj

variable {n : ℕ}

theorem conj_smul (o : 𝓞 E) (x : E) :
    IsCMField.complexConj E (o • x) = IsCMField.ringOfIntegersComplexConj E o • IsCMField.complexConj E x := by
  show IsCMField.complexConj E ((o : E) * x) = _
  rw [map_mul]; rfl

def conjMod (M : Submodule (𝓞 E) E) : Submodule (𝓞 E) E where
  carrier := {x | IsCMField.complexConj E x ∈ M}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show IsCMField.complexConj E (a + b) ∈ M
    rw [map_add]; exact add_mem ha hb
  smul_mem' := fun o x hx => by
    show IsCMField.complexConj E (o • x) ∈ M
    rw [conj_smul]; exact M.smul_mem _ hx

theorem mem_conjMod {M : Submodule (𝓞 E) E} {x : E} : x ∈ conjMod M ↔ IsCMField.complexConj E x ∈ M := Iff.rfl

theorem bar_bar (H : Host E) (o : 𝓞 E) : H.bar (H.bar o) = o := by
  ext; rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem mem_conjId (I : Ideal (𝓞 E)) (o : 𝓞 E) : o ∈ conjId H I ↔ H.bar o ∈ I := by
  rw [conjId, Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa [bar_bar] using hx
  · intro h; exact ⟨_, h, bar_bar H o⟩

theorem conjMod_idlE (H : Host E) (I : Ideal (𝓞 E)) : conjMod (idlE I) = idlE (conjId H I) := by
  ext x
  rw [mem_conjMod]
  constructor
  · rintro ⟨o, ho, h⟩
    refine ⟨H.bar o, (mem_conjId I _).2 (by rwa [bar_bar]), ?_⟩
    have h' : (o : E) = IsCMField.complexConj E x := h
    show ((H.bar o : 𝓞 E) : E) = x
    rw [H.bar_eq, h', IsCMField.complexConj_apply_apply]
  · rintro ⟨o, ho, rfl⟩
    exact ⟨H.bar o, (mem_conjId I _).1 ho, H.bar_eq o⟩

theorem smul_eq_idlE_mul (I : Ideal (𝓞 E)) (M : Submodule (𝓞 E) E) : I • M = idlE I * M := by
  refine le_antisymm (Submodule.smul_le.2 fun a ha x hx => ?_) (Submodule.mul_le.2 ?_)
  · exact Submodule.mul_mem_mul (⟨a, ha, rfl⟩ : (a : E) ∈ idlE I) hx
  · rintro _ ⟨a, ha, rfl⟩ x hx
    exact Submodule.smul_mem_smul ha hx

def conjLat (L : Submodule (𝓞 E) (Fin n → E)) : GenLat E n where
  La :=
  { carrier := {v | (fun j => IsCMField.complexConj E (v j)) ∈ L}
    zero_mem' := by
      show (fun j => IsCMField.complexConj E 0) ∈ L
      rw [map_zero]; exact L.zero_mem
    add_mem' := fun {a b} ha hb => by
      show (fun j => IsCMField.complexConj E (a j + b j)) ∈ L
      simp only [map_add]; exact add_mem ha hb
    smul_mem' := fun o x hx => by
      show (fun j => IsCMField.complexConj E (o • x j)) ∈ L
      simp only [conj_smul]; exact L.smul_mem _ hx }

theorem mem_conjLat {L : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E} :
    v ∈ (conjLat L).La ↔ (fun j => IsCMField.complexConj E (v j)) ∈ L := Iff.rfl

theorem conjLat_conjLat (L : Submodule (𝓞 E) (Fin n → E)) : (conjLat (conjLat L).La).La = L := by
  ext v; simp [mem_conjLat]

theorem latPin_iff_conjLat {Cl : Type} (Lh : Cl → Submodule (𝓞 E) (Fin n → E)) (La : Cl → GenLat E n) :
    LatPin Lh La ↔ ∀ k, La k = conjLat (Lh k) :=
  forall_congr' fun k => ⟨fun h => congrArg GenLat.mk (Submodule.ext h), fun h v => by rw [h, mem_conjLat]⟩

theorem conjLat_std : conjLat (stdLat E n) = ⟨stdLat E n⟩ := by
  have hc (x : E) (hx : IsIntegral ℤ x) : IsIntegral ℤ (IsCMField.complexConj E x) :=
    hx.map_of_comp_eq (RingHom.id ℤ) (IsCMField.complexConj E : E →+* E) (RingHom.ext_int _ _)
  refine congrArg GenLat.mk (Submodule.ext fun v => ?_)
  show _ ∈ stdLat E n ↔ _
  simp only [GlobalTheory.StdHarm.mem_std]
  exact forall_congr' fun j => ⟨fun h => by simpa using hc _ h, hc _⟩

def stdIndex (Λ : GenLat E n) : ℕ := (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index

theorem stdIndex_conjLat (L : Submodule (𝓞 E) (Fin n → E)) : stdIndex (conjLat L) = stdIndex ⟨L⟩ := by
  let f : (Fin n → E) →+ (Fin n → E) := (IsCMField.complexConj E : E →+ E).compLeft (Fin n)
  have h1 : (conjLat L).Ln.toAddSubgroup = (L ⊓ stdLat E n).toAddSubgroup.comap f := by
    ext v
    have : v ∈ stdLat E n ↔ v ∈ (conjLat (stdLat E n)).La := by rw [conjLat_std]
    exact and_congr_right fun _ => this
  have h2 : (conjLat L).La.toAddSubgroup.map f = L.toAddSubgroup := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hv
      refine ⟨f v, ?_, funext fun j => IsCMField.complexConj_apply_apply E (v j)⟩
      rw [← conjLat_conjLat L] at hv
      exact hv
  show AddSubgroup.relIndex _ _ = AddSubgroup.relIndex _ _
  rw [h1, AddSubgroup.relIndex_comap, h2]
  rfl

end Conj

section Scalar

variable (c : Coeff l) {n : ℕ}

theorem absNorm_ne_zero {cc : Ideal (𝓞 E)} (h1 : cc ⊔ conjId H cc = ⊤) : Ideal.absNorm cc ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  rintro rfl
  simp [conjId] at h1

def Guard (H : Host E) (bad : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  (⟨L⟩ : GenLat E n).Unimod ∧ (⟨L⟩ : GenLat E n).TrivAt bad ∧ GenLat.SplitSupp H (⟨L⟩ : GenLat E n)

end Scalar

section Comparison₂

variable (c : Coeff l) {n : ℕ} {T : Type} [AddCommGroup T] [Module c.F T] [Module (𝓞 c.F) T]
  [IsScalarTower (𝓞 c.F) c.F T]

end Comparison₂

section Twist

variable (c : Coeff l) {n : ℕ} {T : Type} [AddCommGroup T] [Module c.F T] [Module (𝓞 c.F) T]
  [IsScalarTower (𝓞 c.F) c.F T]

def unitQuot (H : Host E) (y : ℕ) : E := (1 + y * (H.rt : E)) / (1 - y * (H.rt : E))

end Twist

section Indep

variable (Xo : Moduli Dw l) (c : Coeff l) {n : ℕ}

theorem smul_conjLat_le {m m' : 𝓞 E} (e : (m' : E) = IsCMField.complexConj E (m : E))
    {M M' : Submodule (𝓞 E) (Fin n → E)} (hM : Ideal.span {m} • M ≤ M') :
    Ideal.span {m'} • (conjLat M).La ≤ (conjLat M').La := by
  rw [Submodule.ideal_span_singleton_smul] at hM ⊢
  rintro _ ⟨v, hv, rfl⟩
  have := hM ⟨_, hv, rfl⟩
  rw [mem_conjLat]
  convert this using 1
  funext j
  show IsCMField.complexConj E ((m' : E) * v j) = (m : E) * _
  rw [map_mul, e, IsCMField.complexConj_apply_apply]

theorem guard_conjLat {bad : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} (g : Guard H bad L) :
    Guard H bad (conjLat L).La := by
  obtain ⟨g1, ⟨k, k0, k1, k2⟩, m, m0, m1, m2, m3⟩ := g
  have hs : (conjLat (stdLat E n)).La = stdLat E n := by rw [conjLat_std]
  have hc : ∀ x : E, IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range ↔ x ∈ (algebraMap (𝓞 E) E).range := by
    have : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range → IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range := by
      rintro _ ⟨o, rfl⟩; exact ⟨H.bar o, H.bar_eq o⟩
    exact fun x => ⟨fun h => by simpa using this _ h, this x⟩
  refine ⟨fun v => ?_, ⟨k, k0, ?_, ?_⟩, H.bar m, by simpa using m0, ?_, ?_, fun P hP hm hfix => ?_⟩
  · refine (g1 fun j => IsCMField.complexConj E (v j)).trans ⟨fun h w hw => ?_, fun h w hw => ?_⟩
    · rw [← hc]
      simpa using h _ hw
    · rw [← hc]
      simpa using h (fun j => IsCMField.complexConj E (w j)) (by simpa [mem_conjLat] using hw)
  · exact hs ▸ smul_conjLat_le (by simp) k1
  · exact hs ▸ smul_conjLat_le (by simp) k2
  · exact hs ▸ smul_conjLat_le (H.bar_eq m) m1
  · exact hs ▸ smul_conjLat_le (H.bar_eq m) m2
  · exact m3 P hP (hfix ▸ (mem_conjId P m).2 hm) hfix

variable {Cl : Type} [Fintype Cl] {T : Type} [AddCommGroup T] [Module c.F T]

end Indep

end GlobalTheory.ClassScalarCompare
