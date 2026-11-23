import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup

open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCoinv

section Abstract

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def coFun (s : M →* G) (χ : M →* ℂˣ) (c : W →ₗ[ℂ] W') (f : G → W) (x : M) : W' :=
  (χ x : ℂ) • c (f (s x))

theorem coFun_mem {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hQH : ∀ p ∈ Q, s p ∈ H) (χ : M →* ℂˣ)
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) (f : indSpace H σ) :
    coFun s χ c f.1 ∈ indSpace Q σ' := by
  intro p x
  have h1 : f.1 (s p * s x) = σ ⟨s p, hQH p p.2⟩ (f.1 (s x)) := f.2 ⟨s p, hQH p p.2⟩ (s x)
  show ((χ ((p : M) * x) : ℂˣ) : ℂ) • c (f.1 (s ((p : M) * x))) = σ' p (((χ x : ℂˣ) : ℂ) • c (f.1 (s x)))
  rw [map_mul, map_mul, h1, map_smul, ← hcomp, Units.val_mul, mul_comm, mul_smul]

theorem coFun_smooth {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hs : Continuous s) (hQH : ∀ p ∈ Q, s p ∈ H)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) (f : smoothPart (ind H σ)) :
    (⟨coFun s χ c f.1.1, coFun_mem s hQH χ σ σ' c hcomp f.1⟩ : indSpace Q σ') ∈ smoothPart (ind Q σ') := by
  refine mem_smoothPart_of_nhds (Filter.mem_of_superset
    (((IsOpen.preimage hs f.2).inter hχ).mem_nhds ?_) ?_)
  · refine ⟨?_, one_mem _⟩
    simp
  · rintro x ⟨h1, h2⟩
    have h1' : ind H σ (s x) f.1 = f.1 := h1
    have h2' : χ x = 1 := h2
    apply Subtype.ext
    funext y
    show ((χ (y * x) : ℂˣ) : ℂ) • c (f.1.1 (s (y * x))) = ((χ y : ℂˣ) : ℂ) • c (f.1.1 (s y))
    have h3 : f.1.1 (s y * s x) = f.1.1 (s y) := congrFun (congrArg Subtype.val h1') (s y)
    rw [map_mul, map_mul, h2', mul_one, h3]

end Abstract

section Abstract2

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def coMap {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hs : Continuous s) (hQH : ∀ p ∈ Q, s p ∈ H)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) :
    cIndSpace H σ →ₗ[ℂ] smoothPart (ind Q σ') where
  toFun f := ⟨⟨coFun s χ c f.1.1.1, coFun_mem s hQH χ σ σ' c hcomp f.1.1⟩, coFun_smooth s hs hQH χ hχ σ σ' c hcomp f.1⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show ((χ x : ℂˣ) : ℂ) • c (a.1.1.1 (s x) + b.1.1.1 (s x)) = _
    rw [map_add, smul_add]
    rfl
  map_smul' r a := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show ((χ x : ℂˣ) : ℂ) • c (r • a.1.1.1 (s x)) = r • (((χ x : ℂˣ) : ℂ) • c (a.1.1.1 (s x)))
    rw [map_smul, smul_comm]

theorem coinv_equiv (H U : Subgroup G) (Q : Subgroup M) (s : M →* G) (q : G →* M)
    (hH : IsClosed (H : Set G))
    (hbasis : ∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hs : Continuous s) (hq : Continuous q) (hqs : ∀ x, q (s x) = x) (hker : ∀ g, q g = 1 ↔ g ∈ U)
    (hUH : U ≤ H) (hHQ : ∀ g ∈ H, q g ∈ Q) (hQH : ∀ p ∈ Q, s p ∈ H)
    (C : Set M) (hC : IsCompact C) (hMC : ∀ x : M, ∃ p ∈ Q, ∃ y ∈ C, x = p * y)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (hσ : IsSmooth σ) (σ' : Representation ℂ Q W')
    (c : W →ₗ[ℂ] W') (hc : Function.Surjective c) (hck : ∀ w, c w = 0 ↔ w ∈ twKer σ (U.subgroupOf H) 1)
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w))
    (hK : ∀ f : cIndSpace H σ, (∀ g, f.1.1.1 g ∈ twKer σ (U.subgroupOf H) 1) → f ∈ twKer (cInd H σ) U 1) :
    ∃ E : (cIndSpace H σ ⧸ twKer (cInd H σ) U 1) ≃ₗ[ℂ] smoothPart (ind Q σ'),
      ∀ (f : cIndSpace H σ) (x : M), (E (Submodule.Quotient.mk f)).1.1 x = (χ x : ℂ) • c (f.1.1.1 (s x)) := by
  classical
  haveI hUn : U.Normal := by
    have : U = q.ker := by
      ext g
      rw [MonoidHom.mem_ker, hker]
    rw [this]
    infer_instance
  have hcu : ∀ (u : G) (hu : u ∈ U) (w : W), c (σ ⟨u, hUH hu⟩ w) = c w := by
    intro u hu w
    have : σ ⟨u, hUH hu⟩ w - w ∈ twKer σ (U.subgroupOf H) 1 :=
      Submodule.subset_span ⟨⟨⟨u, hUH hu⟩, hu⟩, w, by simp⟩
    have h2 := (hck _).2 this
    rwa [map_sub, sub_eq_zero] at h2
  have hdec : ∀ g : G, g * (s (q g))⁻¹ ∈ U := by
    intro g
    rw [← hker, map_mul, map_inv, hqs, mul_inv_cancel]
  set Φ := coMap s hs hQH χ hχ σ σ' c hcomp with hΦ
  have hkill : twKer (cInd H σ) U 1 ≤ LinearMap.ker Φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, f, rfl⟩
    show Φ _ = 0
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hn : s x * u * (s x)⁻¹ ∈ U := hUn.conj_mem _ u.2 _
    have e : (cInd H σ (u : G) f).1.1.1 (s x) = σ ⟨_, hUH hn⟩ (f.1.1.1 (s x)) := by
      have := f.1.1.2 ⟨_, hUH hn⟩ (s x)
      rw [← this]
      show f.1.1.1 (s x * u) = f.1.1.1 (s x * u * (s x)⁻¹ * s x)
      congr 1
      group
    show ((χ x : ℂˣ) : ℂ) • c ((cInd H σ (u : G) f - ((1 : U →* ℂˣ) u : ℂ) • f).1.1.1 (s x)) = 0
    have e2 : (cInd H σ (u : G) f - ((1 : U →* ℂˣ) u : ℂ) • f).1.1.1 (s x)
        = (cInd H σ (u : G) f).1.1.1 (s x) - f.1.1.1 (s x) := by
      simp
    rw [e2, e, map_sub, hcu _ hn, sub_self, smul_zero]
  have hinj : ∀ f : cIndSpace H σ, Φ f = 0 → f ∈ twKer (cInd H σ) U 1 := by
    intro f hf
    refine hK f fun g => ?_
    rw [← hck]
    have h1 : ∀ x, c (f.1.1.1 (s x)) = 0 := by
      intro x
      have h2 : ((χ x : ℂˣ) : ℂ) • c (f.1.1.1 (s x)) = 0 := by
        have := congrArg (fun F : smoothPart (ind Q σ') => F.1.1 x) hf
        exact this
      exact (smul_eq_zero.1 h2).resolve_left (Units.ne_zero _)
    have h3 : f.1.1.1 g = σ ⟨_, hUH (hdec g)⟩ (f.1.1.1 (s (q g))) := by
      rw [← f.1.1.2 ⟨_, hUH (hdec g)⟩ (s (q g))]
      congr 1
      group
    rw [h3, hcu _ (hdec g), h1]
  have hmemH : ∀ g, q g ∈ Q → g ∈ H := by
    intro g hg
    have : g = (g * (s (q g))⁻¹) * s (q g) := by group
    rw [this]
    exact mul_mem (hUH (hdec g)) (hQH _ hg)
  let qH : H →* Q := (q.comp H.subtype).codRestrict Q fun h => hHQ h h.2
  let σb : Representation ℂ H W' := twist (σ'.comp qH) (χ.comp (q.comp H.subtype))⁻¹
  have hσb : ∀ (h : H) (w : W'), σb h w = (((χ (q h))⁻¹ : ℂˣ) : ℂ) • σ' (qH h) w := fun h w => rfl
  have hcb : ∀ (h : H) (w : W), c (σ h w) = σb h (c w) := by
    intro h w
    have hp : q h ∈ Q := hHQ h h.2
    have e : h = ⟨_, hUH (hdec h)⟩ * ⟨s (q h), hQH _ hp⟩ := by
      apply Subtype.ext
      show (h : G) = (h : G) * (s (q h))⁻¹ * s (q h)
      group
    have e1 : c (σ h w) = c (σ ⟨s (q h), hQH _ hp⟩ w) := by
      conv_lhs => rw [e, map_mul, Module.End.mul_apply]
      rw [hcu _ (hdec h)]
    rw [e1, hσb]
    have := hcomp ⟨q h, hp⟩ w
    show _ = (((χ (q h))⁻¹ : ℂˣ) : ℂ) • σ' ⟨q h, hp⟩ (c w)
    rw [← this, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hsurj : ∀ φ : smoothPart (ind Q σ'), ∃ f, Φ f = φ := by
    intro φ
    let b : G → W' := fun g => (((χ (q g))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q g)
    have hb : b ∈ indSpace H σb := by
      intro h g
      have h1 : φ.1.1 (q h * q g) = σ' (qH h) (φ.1.1 (q g)) := φ.1.2 (qH h) (q g)
      show (((χ (q ((h : G) * g)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q ((h : G) * g)) = σb h ((((χ (q g))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q g))
      rw [map_mul, h1, map_smul, hσb, map_mul, mul_inv, Units.val_mul, smul_smul, mul_comm]
    have hbs : (⟨b, hb⟩ : indSpace H σb) ∈ smoothPart (ind H σb) := by
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((IsOpen.preimage hq φ.2).inter (IsOpen.preimage hq hχ)).mem_nhds ?_) ?_)
      · refine ⟨?_, ?_⟩
        · simp
        · simp
      · rintro x ⟨h1, h2⟩
        have h1' : ind Q σ' (q x) φ.1 = φ.1 := h1
        have h2' : χ (q x) = 1 := h2
        apply Subtype.ext
        funext y
        show (((χ (q (y * x)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q (y * x)) = (((χ (q y))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q y)
        have h3 : φ.1.1 (q y * q x) = φ.1.1 (q y) := congrFun (congrArg Subtype.val h1') (q y)
        rw [map_mul, map_mul, h2', mul_one, h3]
    have hbc : (⟨⟨b, hb⟩, hbs⟩ : smoothPart (ind H σb)) ∈ cIndSpace H σb := by
      refine ⟨s '' C, hC.image hs, fun g _ => ?_⟩
      obtain ⟨p, hp, y, hy, e⟩ := hMC (q g)
      refine ⟨g * (s y)⁻¹, hmemH _ ?_, s y, ⟨y, hy, rfl⟩, by group⟩
      rw [map_mul, map_inv, hqs, e]
      simpa using hp
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.BZMirOnto.cInd_lift H hH hbasis σ σb c hc hcb (fun w _ => by
      let S : Subgroup H :=
        { carrier := {h | σ h w = w}
          one_mem' := by simp
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
            rw [hb, ha]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq] at *
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      exact ⟨S, hσ w, fun t ht _ => ht⟩) ⟨⟨⟨b, hb⟩, hbs⟩, hbc⟩
    refine ⟨F, Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    show ((χ x : ℂˣ) : ℂ) • c (F.1.1.1 (s x)) = φ.1.1 x
    rw [hF]
    show ((χ x : ℂˣ) : ℂ) • ((((χ (q (s x)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q (s x))) = φ.1.1 x
    rw [hqs, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let L := (twKer (cInd H σ) U 1).liftQ Φ hkill
  have hL : Function.Bijective L := by
    constructor
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (Submodule.Quotient.mk_eq_zero _).2 (hinj f hx)
    · intro φ
      obtain ⟨f, hf⟩ := hsurj φ
      exact ⟨Submodule.Quotient.mk f, hf⟩
  exact ⟨LinearEquiv.ofBijective L hL, fun f x => rfl⟩

end Abstract2

end GlobalTheory.CompanionTheory.CIndCoinv
