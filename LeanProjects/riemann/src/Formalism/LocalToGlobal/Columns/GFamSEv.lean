import Mathlib
import Formalism.LocalToGlobal.Columns.GFamEv
import Formalism.LocalToGlobal.Columns.GFamSH

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

namespace GFamS

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev Pt (F : GFamS K) : Type := Σ b, F.D b

def cls (F : GFamS K) (p : F.Pt) : F.Cl := ⟨p.1, (F.mem p.1).cls p.2⟩

def repPt (F : GFamS K) (c : F.Cl) : F.Pt := ⟨c.1, F.rep c⟩

theorem cls_repPt (F : GFamS K) (c : F.Cl) : F.cls (F.repPt c) = c := by
  obtain ⟨b, c⟩ := c
  exact congrArg (Sigma.mk b) ((F.sec b).spec c)

structure Ev (F : GFamS K) (σ : K →+* ℂ) where

  Y : Type

  ev : F.V →ₛₗ[σ] (Y → ℂ)
  li : LinearIndependent ℂ fun i => ev (F.bV i)

  ip : (Y → ℂ) →ₗ⋆[ℂ] (Y → ℂ) →ₗ[ℂ] ℂ
  ip_ev : ∀ x y, ip (ev x) (ev y) = σ (F.pair x y)

  tr : ∀ b, F.G b →* ((Y → ℂ) ≃ₗ[ℂ] (Y → ℂ))
  tr_ev : ∀ b g x, tr b g (ev x) = ev (F.ρ b g x)

namespace Ev

variable {F : GFamS K} {σ : K →+* ℂ} (E : F.Ev σ)

@[reducible] def mem (b : F.β) : (F.mem b).Ev σ where
  Y := E.Y
  ev := E.ev
  li := E.li
  ip := E.ip
  ip_ev := E.ip_ev
  tr := E.tr b
  tr_ev := E.tr_ev b

theorem mem_Y (b : F.β) : (E.mem b).Y = E.Y := rfl
theorem mem_ev (b : F.β) : (E.mem b).ev = E.ev := rfl
theorem mem_ip (b : F.β) : (E.mem b).ip = E.ip := rfl
theorem mem_tr (b : F.β) : (E.mem b).tr = E.tr b := rfl

@[reducible] def ofMem {b₀ : F.β} (E₀ : (F.mem b₀).Ev σ) (tr : ∀ b, F.G b →* ((E₀.Y → ℂ) ≃ₗ[ℂ] (E₀.Y → ℂ)))
    (tr_ev : ∀ b g x, tr b g (E₀.ev x) = E₀.ev (F.ρ b g x)) : F.Ev σ where
  Y := E₀.Y
  ev := E₀.ev
  li := E₀.li
  ip := E₀.ip
  ip_ev := E₀.ip_ev
  tr := tr
  tr_ev := tr_ev

def evCl : (F.Cl → F.V) →ₛₗ[σ] (F.Cl → E.Y → ℂ) where
  toFun f := fun c => E.ev (f c)
  map_add' f g := by funext c; exact map_add E.ev _ _
  map_smul' a f := by funext c; exact LinearMap.map_smulₛₗ E.ev _ _

def emb : F.Forms →ₛₗ[σ] (F.Cl → E.Y → ℂ) where
  toFun φ := fun c => E.ev (F.valAt φ c)
  map_add' φ ψ := by funext c; exact map_add E.ev _ _
  map_smul' a φ := by funext c; exact LinearMap.map_smulₛₗ E.ev _ _

theorem emb_apply (φ : F.Forms) (c : F.Cl) :
    E.emb φ c = E.ev (((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) ((F.sec c.1).rep c.2)) := rfl

theorem emb_valAt (φ : F.Forms) (c : F.Cl) : E.emb φ c = E.ev (F.valAt φ c) := rfl

def part (b : F.β) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] ((F.mem b).Cl → E.Y → ℂ) :=
  LinearMap.pi fun c => LinearMap.proj (⟨b, c⟩ : F.Cl)

theorem part_apply (b : F.β) (Φ : F.Cl → E.Y → ℂ) (c : (F.mem b).Cl) : E.part b Φ c = Φ ⟨b, c⟩ := rfl

def trPt (p : F.Pt) : (E.Y → ℂ) ≃ₗ[ℂ] (E.Y → ℂ) := E.tr p.1 ((F.sec p.1).mv p.2)

def atPt (p : F.Pt) (Φ : F.Cl → E.Y → ℂ) : E.Y → ℂ := E.trPt p (Φ (F.cls p))

theorem atPt_emb (φ : F.Forms) (p : F.Pt) :
    E.atPt p (E.emb φ) = E.ev (((φ p.1 : (F.mem p.1).EqFun) : F.D p.1 → F.V) p.2) := by
  unfold atPt trPt
  rw [emb_apply, E.tr_ev]
  show E.ev (F.ρ p.1 ((F.sec p.1).mv p.2) (((φ p.1 : (F.mem p.1).EqFun) : F.D p.1 → F.V) ((F.sec p.1).rep ((F.mem p.1).cls p.2)))) = _
  rw [← (φ p.1).2, (F.sec p.1).mv_smul]

theorem atPt_eq (hf : F.Free) (Φ : F.Cl → E.Y → ℂ) (b : F.β) (d : F.D b) (c : (F.mem b).Cl) (g : F.G b)
    (h : g • (F.sec b).rep c = d) : E.atPt ⟨b, d⟩ Φ = E.tr b g (Φ ⟨b, c⟩) := by
  have hc : (F.mem b).cls d = c := by rw [← h, (F.mem b).cls_smul, (F.sec b).spec]
  subst hc
  have h1 : (F.sec b).mv d = g := by
    have h2 : (g⁻¹ * (F.sec b).mv d) • (F.sec b).rep ((F.mem b).cls d) = (F.sec b).rep ((F.mem b).cls d) := by
      rw [mul_smul, (F.sec b).mv_smul]
      conv_lhs => rw [← h]
      rw [inv_smul_smul]
    have h3 := hf b _ _ h2
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  show E.tr b ((F.sec b).mv d) (Φ ⟨b, (F.mem b).cls d⟩) = _
  rw [h1]

def opOn (δ : F.Pt → F.Pt) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] (F.Cl → E.Y → ℂ) where
  toFun Φ := fun c => E.atPt (δ (F.repPt c)) Φ
  map_add' Φ Ψ := by funext c; exact map_add (E.trPt _) _ _
  map_smul' a Φ := by funext c; exact map_smul (E.trPt _) _ _

theorem opOn_apply (δ : F.Pt → F.Pt) (Φ : F.Cl → E.Y → ℂ) (c : F.Cl) :
    E.opOn δ Φ c = E.trPt (δ (F.repPt c)) (Φ (F.cls (δ (F.repPt c)))) := rfl

theorem opOn_emb (δ : F.Pt → F.Pt) (φ : F.Forms) (c : F.Cl) :
    E.opOn δ (E.emb φ) c =
      E.ev (((φ (δ (F.repPt c)).1 : (F.mem (δ (F.repPt c)).1).EqFun) : F.D (δ (F.repPt c)).1 → F.V) (δ (F.repPt c)).2) :=
  E.atPt_emb φ _

theorem opOn_id (hf : F.Free) : E.opOn (fun p => p) = LinearMap.id := by
  ext Φ c : 2
  obtain ⟨b, c⟩ := c
  show E.atPt ⟨b, (F.sec b).rep c⟩ Φ = Φ ⟨b, c⟩
  rw [E.atPt_eq hf Φ b _ c 1 (one_smul _ _), map_one]
  rfl

theorem opOn_comp (hf : F.Free) (δ δ' : F.Pt → F.Pt)
    (hδ' : ∀ (b : F.β) (g : F.G b) (d : F.D b), ∃ g' : F.G (δ' ⟨b, d⟩).1,
      δ' ⟨b, g • d⟩ = ⟨(δ' ⟨b, d⟩).1, g' • (δ' ⟨b, d⟩).2⟩ ∧ E.tr _ g' = E.tr b g) :
    E.opOn δ ∘ₗ E.opOn δ' = E.opOn fun p => δ' (δ p) := by
  ext Φ c : 2
  show E.trPt (δ (F.repPt c)) (E.atPt (δ' (F.repPt (F.cls (δ (F.repPt c))))) Φ) = E.atPt (δ' (δ (F.repPt c))) Φ
  generalize δ (F.repPt c) = p
  obtain ⟨b, d⟩ := p
  obtain ⟨g', h1, h2⟩ := hδ' b ((F.sec b).mv d) ((F.sec b).rep ((F.mem b).cls d))
  rw [(F.sec b).mv_smul d] at h1
  rw [h1]
  show E.tr b ((F.sec b).mv d) (E.atPt (δ' ⟨b, (F.sec b).rep ((F.mem b).cls d)⟩) Φ) = _
  generalize δ' ⟨b, (F.sec b).rep ((F.mem b).cls d)⟩ = q at g' h2
  obtain ⟨b', d'⟩ := q
  rw [E.atPt_eq hf Φ b' (g' • d') ((F.mem b').cls d') (g' * (F.sec b').mv d')
    (by rw [mul_smul, (F.sec b').mv_smul]), map_mul, h2]
  rfl

def opOnC (δ : ∀ b, F.D b → F.D b) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] (F.Cl → E.Y → ℂ) := E.opOn fun p => ⟨p.1, δ p.1 p.2⟩

theorem opOnC_apply (δ : ∀ b, F.D b → F.D b) (Φ : F.Cl → E.Y → ℂ) (c : F.Cl) :
    E.opOnC δ Φ c = E.trPt ⟨c.1, δ c.1 (F.rep c)⟩ (Φ ⟨c.1, (F.mem c.1).cls (δ c.1 (F.rep c))⟩) := rfl

theorem opOnC_emb (δ : ∀ b, F.D b → F.D b) (φ : F.Forms) (c : F.Cl) :
    E.opOnC δ (E.emb φ) c = E.ev (((φ c.1 : (F.mem c.1).EqFun) : F.D c.1 → F.V) (δ c.1 (F.rep c))) :=
  E.atPt_emb φ ⟨c.1, δ c.1 (F.rep c)⟩

theorem opOnC_id (hf : F.Free) : E.opOnC (fun _ d => d) = LinearMap.id := E.opOn_id hf

theorem opOnC_comp (hf : F.Free) (δ δ' : ∀ b, F.D b → F.D b)
    (hδ' : ∀ (b : F.β) (g : F.G b) (d : F.D b), δ' b (g • d) = g • δ' b d) :
    E.opOnC δ ∘ₗ E.opOnC δ' = E.opOnC fun b d => δ' b (δ b d) :=
  E.opOn_comp hf _ _ fun b g d => ⟨g, by rw [hδ'], rfl⟩

def lin : (F.ιV → ℂ) →ₗ[ℂ] (E.Y → ℂ) := Fintype.linearCombination ℂ fun i => E.ev (F.bV i)

theorem ev_eq_lin (x : F.V) : E.ev x = E.lin fun i => σ (F.bV.repr x i) := by
  conv_lhs => rw [← F.bV.sum_repr x]
  rw [map_sum, lin, Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ E.ev _ _

theorem lin_ker : LinearMap.ker E.lin = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact E.li.fintypeLinearCombination_injective

def gram : Matrix F.ιV F.ιV ℂ := Matrix.of fun i j => E.ip (E.ev (F.bV i)) (E.ev (F.bV j))

def ipB : (E.Y → ℂ) →ₗ[ℂ] (F.ιV → ℂ) := LinearMap.pi fun j => E.ip (E.ev (F.bV j))

open Classical in

def co : (E.Y → ℂ) →ₗ[ℂ] (F.ιV → ℂ) :=
  if IsUnit E.gram.det then Matrix.toLin' E.gram⁻¹ ∘ₗ E.ipB
  else (E.lin.exists_leftInverse_of_injective E.lin_ker).choose

def extend {M : Type} [AddCommGroup M] [Module ℂ M] (ℓ : F.V →ₛₗ[σ] M) : (E.Y → ℂ) →ₗ[ℂ] M :=
  (Fintype.linearCombination ℂ fun i => ℓ (F.bV i)) ∘ₗ E.co

def sharp (ℓ : F.V →ₛₗ[σ] ℂ) : E.Y → ℂ :=
  ∑ j, starRingEnd ℂ (∑ i, ℓ (F.bV i) * E.gram⁻¹ i j) • E.ev (F.bV j)

theorem lin_mem (b : F.β) : (E.mem b).lin = E.lin := rfl
theorem gram_mem (b : F.β) : (E.mem b).gram = E.gram := rfl
theorem ipB_mem (b : F.β) : (E.mem b).ipB = E.ipB := rfl
theorem co_mem (b : F.β) : (E.mem b).co = E.co := rfl
theorem extend_mem (b : F.β) {M : Type} [AddCommGroup M] [Module ℂ M] (ℓ : F.V →ₛₗ[σ] M) :
    (E.mem b).extend ℓ = E.extend ℓ := rfl
theorem sharp_mem (b : F.β) (ℓ : F.V →ₛₗ[σ] ℂ) : (E.mem b).sharp ℓ = E.sharp ℓ := rfl

theorem ipB_lin (z : F.ιV → ℂ) : E.ipB (E.lin z) = E.gram *ᵥ z := by
  funext j
  simp only [ipB, LinearMap.pi_apply, lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smul, smul_eq_mul,
    Matrix.mulVec, dotProduct, gram, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem co_lin (z : F.ιV → ℂ) : E.co (E.lin z) = z := by
  unfold co
  split_ifs with hG
  · rw [LinearMap.comp_apply, ipB_lin, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG,
      Matrix.one_mulVec]
  · exact LinearMap.congr_fun (E.lin.exists_leftInverse_of_injective E.lin_ker).choose_spec z

theorem extend_eq_ip (hG : IsUnit E.gram.det) (ℓ : F.V →ₛₗ[σ] ℂ) (f : E.Y → ℂ) : E.extend ℓ f = E.ip (E.sharp ℓ) f := by
  unfold extend co sharp
  rw [if_pos hG]
  simp only [LinearMap.comp_apply, Fintype.linearCombination_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, ipB,
    LinearMap.pi_apply, smul_eq_mul, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    RingHomCompTriple.comp_apply, RingHom.id_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem extend_ev {M : Type} [AddCommGroup M] [Module ℂ M] (ℓ : F.V →ₛₗ[σ] M) (x : F.V) : E.extend ℓ (E.ev x) = ℓ x := by
  rw [extend, LinearMap.comp_apply, ev_eq_lin, co_lin, Fintype.linearCombination_apply]
  conv_rhs => rw [← F.bV.sum_repr x]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (LinearMap.map_smulₛₗ ℓ _ _).symm

def ipCl (h : F.Ok) : (F.Cl → E.Y → ℂ) →ₗ⋆[ℂ] (F.Cl → E.Y → ℂ) →ₗ[ℂ] ℂ :=
  letI := h.fintypeCl
  ∑ c : F.Cl, ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ •
    ((E.ip.comp (LinearMap.proj c)).compl₂ (LinearMap.proj c))

theorem ipCl_apply (h : F.Ok) (Φ Ψ : F.Cl → E.Y → ℂ) :
    E.ipCl h Φ Ψ = (letI := h.fintypeCl
      ∑ c : F.Cl, ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ * E.ip (Φ c) (Ψ c)) := by
  unfold ipCl
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    smul_eq_mul]

def Fi : Submodule ℂ (F.Cl → E.Y → ℂ) := Submodule.span ℂ (Set.range E.emb)

theorem emb_li (h : F.Ok) {κ : Type} (v : κ → F.Forms) (hv : LinearIndependent K v) :
    LinearIndependent ℂ fun a => E.emb (v a) := by
  classical
  let _ : Fintype F.Cl := h.fintypeCl
  let Bb : Basis (Σ _ : F.Cl, F.ιV) K (F.Cl → F.V) := Pi.basis fun _ => F.bV
  have h1 : LinearIndependent ℂ fun i => E.evCl (Bb i) := by
    have e : (fun i => E.evCl (Bb i)) = fun ji : (Σ _ : F.Cl, F.ιV) => Pi.single ji.1 (E.ev (F.bV ji.2)) := by
      funext ⟨c, i⟩
      funext c'
      simp only [Bb, Pi.basis_apply, evCl, LinearMap.coe_mk, AddHom.coe_mk]
      by_cases hc : c' = c
      · subst hc; simp
      · simp [Pi.single_eq_of_ne hc]
    rw [e]
    exact Pi.linearIndependent_single (fun _ i => E.ev (F.bV i)) fun _ => E.li
  exact rec_li_semilin σ E.evCl Bb h1 (fun a => F.evRep h (v a))
    (hv.map' (F.evRep h) (LinearMap.ker_eq_bot.2 (F.evRep_injective h)))

theorem span_basis {ι : Type} [Fintype ι] (b : Basis ι K F.Forms) :
    Submodule.span ℂ (Set.range fun a => E.emb (b a)) = E.Fi := by
  refine le_antisymm (Submodule.span_mono ?_) ?_
  · rintro _ ⟨a, rfl⟩
    exact ⟨b a, rfl⟩
  · unfold Fi
    rw [Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    rw [← b.sum_repr φ, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem finrank_Fi (h : F.Ok) : finrank ℂ E.Fi = F.hDim h := by
  rw [← E.span_basis (F.hB h), finrank_span_eq_card (E.emb_li h _ (F.hB h).linearIndependent), Fintype.card_fin]

def evAt {ι : Type} (pts : ι → F.Pt) : (F.Cl → E.Y → ℂ) →ₗ[ℂ] (ι → E.Y → ℂ) :=
  LinearMap.pi fun i => (E.trPt (pts i)).toLinearMap ∘ₗ LinearMap.proj (F.cls (pts i))

theorem evAt_apply {ι : Type} (pts : ι → F.Pt) (Φ : F.Cl → E.Y → ℂ) (i : ι) : E.evAt pts Φ i = E.atPt (pts i) Φ := rfl

def perCl (h : F.Ok) {ι : Type} [Fintype ι] (ℓ : F.Cl → ι → (F.V →ₛₗ[σ] ℂ)) :
    (F.Cl → E.Y → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ :=
  letI := h.fintypeCl
  LinearMap.mk₂ ℂ (fun Φ z => ∑ c : F.Cl,
      ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ * ∑ a, z a * E.extend (ℓ c a) (Φ c))
    (fun Φ Φ' z => by simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (fun a Φ z => by
      simp only [Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      ring)
    (fun Φ z z' => by simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib])
    (fun a Φ z => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      ring)

theorem perCl_apply (h : F.Ok) {ι : Type} [Fintype ι] (ℓ : F.Cl → ι → (F.V →ₛₗ[σ] ℂ)) (Φ : F.Cl → E.Y → ℂ) (z : ι → ℂ) :
    E.perCl h ℓ Φ z = (letI := h.fintypeCl
      ∑ c : F.Cl, ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ *
        ∑ a, z a * E.extend (ℓ c a) (Φ c)) := rfl

theorem perCl_emb (h : F.Ok) {ι : Type} [Fintype ι] (ℓ : F.Cl → ι → (F.V →ₛₗ[σ] ℂ)) (φ : F.Forms) (z : ι → ℂ) :
    E.perCl h ℓ (E.emb φ) z = (letI := h.fintypeCl
      ∑ c : F.Cl, ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ *
        ∑ a, z a * ℓ c a (F.valAt φ c)) := by
  unfold perCl
  simp only [LinearMap.mk₂_apply, emb_valAt, extend_ev]

theorem norm_eq (h : F.Ok) (R : F.Rat) (hσ : ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) (φ : F.Forms) :
    (majAt (F.hB h) (stdFrame (F.hGram h)) (InfinitePlace.mk σ) φ φ).re =
      (letI := h.fintypeCl
       ∑ c : F.Cl, ((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ *
        E.ip (E.emb φ c) (E.emb φ c)).re := by
  let _ := h.fintypeCl
  rw [R.maj_eq h]
  unfold ipAt
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [F.wt_eq_card h c, emb_valAt, E.ip_ev]
  rcases (F.mem c.1).pairAt_mk σ hσ with hp | hp
  · exact congrArg (fun z : ℂ => (((Nat.card (MulAction.stabilizer (F.G c.1) (F.rep c)) : ℕ) : ℂ)⁻¹ * z).re) (hp _ _)
  · have e : F.pairAt (InfinitePlace.mk σ) (F.valAt φ c) (F.valAt φ c) = starRingEnd ℂ (σ (F.pair (F.valAt φ c) (F.valAt φ c))) := hp _ _
    rw [e, ← Complex.conj_re]
    congr 1
    simp only [map_mul, map_inv₀, map_natCast, Complex.conj_conj]

theorem norm_ipCl (h : F.Ok) (R : F.Rat) (hσ : ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) (φ : F.Forms) :
    (majAt (F.hB h) (stdFrame (F.hGram h)) (InfinitePlace.mk σ) φ φ).re = (E.ipCl h (E.emb φ) (E.emb φ)).re := by
  rw [ipCl_apply]
  exact E.norm_eq h R hσ φ

end Ev

end GFamS

end Formalism.L2.Col
