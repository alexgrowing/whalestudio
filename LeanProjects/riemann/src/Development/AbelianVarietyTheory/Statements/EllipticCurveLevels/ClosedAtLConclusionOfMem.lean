import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC

namespace GlobalTheory.Cong

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def Apart (w u : HeightOneSpectrum (𝓞 E)) : Prop :=
  w.under (𝓞 (maximalRealSubfield E)) ≠ u.under (𝓞 (maximalRealSubfield E))

omit [IsAlgClosure E Ω] in

def SplitAtt (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ IsSSRep r ∧ ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ B, (CG.mk π).HasSat w B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)

omit [IsCMField E] [IsAlgClosure E Ω] in

def SstAt (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
    IsSstAt P Bw (r.comp (Dec (F := E) A).subtype)

def IwaAt (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ σ, π.IsLocComp w σ ∧ PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥

def ScAt (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ σ, π.IsLocComp w σ ∧ SmGL.IsCuspidal σ.ρ

def Seed : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → ScAt π w₀ →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), SplitAtt π ι r ∧ ∀ w, IsSplitAt w → Apart w w₀ →
      ClauseAt .ss π ι r w ∧ ClauseAt .dR π ι r w ∧ ClauseAt .crys π ι r w ∧ (IwaAt π w → SstAt r w)

structure Match (U : Submodule ℂ (UA E a → ℂ)) (π : CuspSub E a) : Prop where
  aut : IsAutRepU U
  unram : ∀ w, ¬ IsSplitAt w → IsUnramU U w
  split : ∀ w, IsSplitAt w → ∀ σ, π.IsLocComp w σ → IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ
  inf : ∀ τ lam, HasWeightAt U τ lam → (CG.mk π).infChar τ = infOfWeight lam

def Desc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), l.Prime → 1 ≤ a → ∀ π : CuspSub E a,
    InScope .csd l π (quadChar E ^ a) → ∃ U : Submodule ℂ (UA E a → ℂ), Match U π

def ScU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧ SmGL.IsCuspidal σ.ρ

def BCBack : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ a : ℕ, 1 ≤ a → ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → IsUnramU U w) →
    ∀ w₀, IsSplitAt w₀ → ScU U w₀ →
    ∃ π : CuspSub E a, Match U π ∧ GlobalTheory.ContraPair.PolarizedPair π (quadChar E ^ a) ∧
      ∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B

structure IsLevelAway (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) : Prop where
  fin : K ≤ finU E a
  one : ∀ x ∈ K, ∀ u, ¬ Apart u w₀ → cLoc u x = 1
  compact : IsCompact (K : Set (UA E a))
  isOpen : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ ∀ x ∈ N, x ∈ finU E a → (∀ u, ¬ Apart u w₀ → cLoc u x = 1) → x ∈ K

def IsIntegralOp (ι : Qbar l ≃+* ℂ) (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU E a ∧ (∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal → cLoc u g = 1) ∧ ‖ι.symm (f g)‖ ≤ 1

def ActsBy {J : Type} (K : Subgroup (UA E a)) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ) : Prop :=
  ∀ U, IsAutRepU U → ∀ φ ∈ U, (∀ x ∈ K, RU E a x φ = φ) → ∀ j, opOf (RU E a) (t j) φ = η U j • φ

structure OfType (lam : (E →+* ℂ) → DomWeight a) (K : Subgroup (UA E a)) (U : Submodule ℂ (UA E a → ℂ)) : Prop where
  aut : IsAutRepU U
  wt : ∀ τ, HasWeightAt U τ (lam τ)
  fix : ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K, RU E a x φ = φ

def CongU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam : (E →+* ℂ) → DomWeight a) (J : Type) (t : J → (UA E a →₀ ℂ))
      (η : Submodule ℂ (UA E a → ℂ) → J → ℂ), (∀ j, IsIntegralOp ι (t j)) → ActsBy K t η → ∀ U, OfType lam K U →
      PolyApprox (fun j => ι.symm (η U j)) {θ | ∃ U', OfType lam K U' ∧ ScU U' w₀ ∧ θ = fun j => ι.symm (η U' j)}

def FinU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)), IsLevelAway w₀ K →
    ∀ (lam : (E →+* ℂ) → DomWeight a) (J : Type) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ),
      (∀ j, ∀ g ∈ (t j).support, g ∈ finU E a ∧ ∃ q : ℚ, t j g = q) → ActsBy K t η → ∀ U, OfType lam K U →
      ∃ L : FinExt l, ∀ j, ι.symm (η U j) ∈ L.1

def CentreTrace : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (a : ℕ) (K : Subgroup (GL (Fin a) (w.adicCompletion E))), IsOpen (K : Set (GL (Fin a) (w.adicCompletion E))) →
    IsCompact (K : Set (GL (Fin a) (w.adicCompletion E))) → ∀ g : Weil h, ∃ f : GL (Fin a) (w.adicCompletion E) →₀ ℂ,
      ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), ∀ v ∈ PRep.fixed σ.ρ K,
        opOf σ.ρ f v = (-((rc (algNorm σ)).charPol g).nextCoeff) • v

def ClosedAtL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
    ∀ (J : (E →+* Qbar l) → Multiset ℤ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r →
    ∀ C : Set (G E Ω →* GL (Fin a) (Qbar l)), LinApprox r C →
      (∀ ρ ∈ C, Continuous ρ ∧ IsSstAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) →
      (IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (J τ)) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype)) → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype))

def ClosedDR : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
    ∀ (h : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r →
    ∀ C : Set (G E Ω →* GL (Fin a) (Qbar l)), LinApprox r C →
      (∀ ρ ∈ C, Continuous ρ ∧ IsSstAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          ∃ J' : Multiset ℤ, IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ J' ∧ ∀ n ∈ J', |n| ≤ h) →
      IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype)) → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype))

def JumpsKept : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ), 1 ≤ a →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
    ∀ (J : (E →+* Qbar l) → Multiset ℤ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) →
    ∀ C : Set (G E Ω →* GL (Fin a) (Qbar l)), LinApprox r C →
      (∀ ρ ∈ C, Continuous ρ ∧ IsSstAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) →
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (J τ)

theorem closedAtL_of (H₁ : ClosedDR) (H₂ : JumpsKept) : ClosedAtL := by
  intro E Ω _ _ _ _ _ l _ a ha P AI hT w A hA O _ _ _ Bw hBw J r hr hss C hC hρ
  classical
  set h : ℕ := Finset.univ.sup fun τ : E →+* Qbar l => ((J τ).map Int.natAbs).sum
  have hb : ∀ τ, ∀ n ∈ J τ, |n| ≤ h := fun τ n hn => by
    have h1 : n.natAbs ≤ ((J τ).map Int.natAbs).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hn)
    have h2 : ((J τ).map Int.natAbs).sum ≤ h :=
      Finset.le_sup (f := fun τ : E →+* Qbar l => ((J τ).map Int.natAbs).sum) (Finset.mem_univ τ)
    rw [Int.abs_eq_natAbs]; exact_mod_cast h1.trans h2
  have hdr := H₁ E Ω l a ha P AI hT w A hA O Bw hBw h r hr hss C hC fun ρ hm =>
    ⟨(hρ ρ hm).1, (hρ ρ hm).2.1, fun τ LL' τ' hi => ⟨J τ, (hρ ρ hm).2.2 τ LL' τ' hi, hb τ⟩⟩
  exact ⟨⟨hdr.1, H₂ E Ω l a ha P AI hT w A hA O Bw hBw J r hr hdr.1 C hC fun ρ hm =>
    ⟨(hρ ρ hm).1, (hρ ρ hm).2.1, (hρ ρ hm).2.2⟩⟩, hdr.2⟩

theorem closedAtL_conclusion_of_mem {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ}
    [Fact l.Prime] {a : ℕ} {P : LocPrime l} {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (J : (E →+* Qbar l) → Multiset ℤ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (C : Set (G E Ω →* GL (Fin a) (Qbar l))) (hrC : r ∈ C)
    (hρ : ∀ ρ ∈ C, Continuous ρ ∧ IsSstAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ (J τ)) :
    LinApprox r C ∧ (IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (J τ)) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype)) → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)) := by
  let τ₀ : E →+* Qbar l := Bw.j.comp (algebraMap E Ω)
  have hi : IsInduced Bw τ₀ (AlgHom.id ℚ_[l] ↥Bw.Kw.1) := fun x => rfl
  obtain ⟨LL', r', hm, hd, -⟩ := (hρ r hrC).2.2 τ₀ Bw.Kw _ hi
  exact ⟨linApprox_of_mem hrC, ⟨⟨LL', r', hm, hd⟩, (hρ r hrC).2.2⟩, fun hc => hc r hrC⟩

theorem eq_of_linApprox {k k' Γ : Type} [NormedField k] [NormedField k'] [IsUltrametricDist k'] [Group Γ] {a : ℕ}
    (ha : (a : k) ≠ 0) (σ : k →+* k') (hσ : ∀ x, ‖σ x‖ = ‖x‖) {r : Γ →* GL (Fin a) k} {C : Set (Γ →* GL (Fin a) k)}
    (hr : LinApprox r C) (B : ℝ) (α β : k')
    (hx : ∀ s : Finset (Γ →* GL (Fin a) k), (s : Set (Γ →* GL (Fin a) k)) ⊆ C → ∃ x : Γ →₀ k', (∀ g, ‖x g‖ ≤ B) ∧
      x.sum (fun g c => c * σ (trc r g)) = α ∧ ∀ ρ ∈ s, x.sum (fun g c => c * σ (trc ρ g)) = β) : α = β := by
  by_contra hne
  have hd : 0 < ‖α - β‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have ha' : 0 < ‖(a : k)‖ := norm_pos_iff.2 ha
  set B' := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  set q := ‖β‖ / ‖(a : k)‖
  have hq : 0 ≤ q := by positivity
  set ε : ℝ := ‖α - β‖ / (2 * (B' + 1) * (q + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hεeq : ε * (2 * (B' + 1) * (q + 1)) = ‖α - β‖ := div_mul_cancel₀ _ (by positivity)
  obtain ⟨s, c, hs, hc⟩ := hr ε hε0
  obtain ⟨x, hxB, hα, hβ⟩ := hx s hs
  set S := ∑ ρ ∈ s, σ (c ρ)
  have key : α - S * β = ∑ g ∈ x.support, x g * σ (trc r g - ∑ ρ ∈ s, c ρ * trc ρ g) := by
    have hSβ : S * β = ∑ ρ ∈ s, σ (c ρ) * x.sum (fun g c' => c' * σ (trc ρ g)) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun ρ hρ => by rw [hβ ρ hρ]
    rw [hSβ, ← hα]
    simp only [Finsupp.sum, map_sub, map_sum, map_mul, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun g _ => by ring
  have h1 : ‖α - S * β‖ ≤ B' * ε := by
    rw [key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun g _ => ?_
    rw [norm_mul, hσ]
    exact mul_le_mul ((hxB g).trans (le_max_left _ _)) (hc g) (norm_nonneg _) hB'
  have h2 : ‖(1 : k') - S‖ * ‖(a : k)‖ ≤ ε := by
    have := hc 1
    have t1 : ∀ ρ : Γ →* GL (Fin a) k, trc ρ 1 = a := fun ρ => by simp [trc]
    have e : trc r 1 - ∑ ρ ∈ s, c ρ * trc ρ 1 = (a : k) * (1 - ∑ ρ ∈ s, c ρ) := by
      rw [t1, Finset.sum_congr rfl fun ρ _ => by rw [t1 ρ], mul_sub, mul_one, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [e, norm_mul] at this
    have e2 : (1 : k') - S = σ (1 - ∑ ρ ∈ s, c ρ) := by simp [S, map_sum]
    rw [e2, hσ, mul_comm]; exact this
  have h3 : ‖(S - 1) * β‖ ≤ ε * q := by
    rw [norm_mul, ← norm_neg (S - 1), neg_sub]
    have : ‖(1 : k') - S‖ ≤ ε / ‖(a : k)‖ := by rw [le_div_iff₀ ha']; exact h2
    calc ‖(1 : k') - S‖ * ‖β‖ ≤ ε / ‖(a : k)‖ * ‖β‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ε * q := by rw [div_mul_eq_mul_div, mul_div_assoc]
  have e3 : α - β = (α - S * β) + (S - 1) * β := by ring
  have h4 : ‖α - β‖ ≤ max (B' * ε) (ε * q) := by
    rw [e3]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h1 h3)
  have h5 : B' * ε < ‖α - β‖ := by nlinarith [mul_nonneg hB' hq, mul_pos hε0 (by positivity : (0:ℝ) < (B' + 1) * (q + 1))]
  have h6 : ε * q < ‖α - β‖ := by nlinarith [mul_nonneg hB' hq, mul_pos hε0 (by positivity : (0:ℝ) < (B' + 1) * (q + 1))]
  exact absurd h4 (not_le.2 (max_lt h5 h6))

theorem multiset_eq_of_powSum {F : Type} [Field F] [CharZero F] {S : Set F} (hS : S.Infinite) (h0 : ∀ z ∈ S, z ≠ 0)
    (J J' : Multiset ℤ) (h : ∀ z ∈ S, (J.map (z ^ ·)).sum = (J'.map (z ^ ·)).sum) : J = J' := by
  classical
  set N : ℕ := ((J + J').map Int.natAbs).sum
  have hN : ∀ n ∈ J + J', 0 ≤ n + N := fun n hn => by
    have : n.natAbs ≤ N := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hn)
    omega
  set f : ℤ → ℕ := fun n => (n + N).toNat
  let p : Multiset ℤ → Polynomial F := fun M => ((M.map f).map fun k => Polynomial.X ^ k).sum
  have ev : ∀ M : Multiset ℤ, (∀ n ∈ M, 0 ≤ n + N) → ∀ z : F, z ≠ 0 →
      (p M).eval z = z ^ N * (M.map (z ^ ·)).sum := by
    intro M hM z hz
    rw [show (p M).eval z = Polynomial.evalRingHom z (p M) from rfl]
    simp only [p, map_multiset_sum, Multiset.map_map, Function.comp_def, map_pow, Polynomial.coe_evalRingHom,
      Polynomial.eval_X]
    rw [← Multiset.sum_map_mul_left]
    congr 1
    refine Multiset.map_congr rfl fun n hn => ?_
    have h1 : ((f n : ℕ) : ℤ) = n + N := Int.toNat_of_nonneg (hM n hn)
    rw [Polynomial.eval_pow, Polynomial.eval_X, ← zpow_natCast, h1, zpow_add₀ hz, zpow_natCast, mul_comm]
  have hJ : ∀ n ∈ J, 0 ≤ n + N := fun n hn => hN n (Multiset.mem_add.2 (Or.inl hn))
  have hJ' : ∀ n ∈ J', 0 ≤ n + N := fun n hn => hN n (Multiset.mem_add.2 (Or.inr hn))
  have hp : p J = p J' := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ (hS.mono fun z hz => ?_)
    simp only [Set.mem_setOf_eq]
    rw [ev J hJ z (h0 z hz), ev J' hJ' z (h0 z hz), h z hz]
  have coeff : ∀ (m : Multiset ℕ) (i : ℕ), ((m.map fun k => Polynomial.X ^ k).sum : Polynomial F).coeff i = (m.count i : F) := by
    intro m i
    induction m using Multiset.induction_on with
    | empty => simp
    | cons k m ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Polynomial.coeff_add, ih, Polynomial.coeff_X_pow, Multiset.count_cons]
      split_ifs <;> simp_all [add_comm] <;> omega
  have hm : J.map f = J'.map f := by
    ext i
    have := congrArg (fun P : Polynomial F => P.coeff i) hp
    simp only [p, coeff] at this
    exact_mod_cast this
  have back : ∀ M : Multiset ℤ, (∀ n ∈ M, 0 ≤ n + N) → (M.map f).map (fun k : ℕ => (k : ℤ) - N) = M := by
    intro M hM
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id M]
    refine Multiset.map_congr rfl fun n hn => ?_
    simp only [Function.comp_apply, id, f]
    rw [Int.toNat_of_nonneg (hM n hn)]; ring
  rw [← back J hJ, ← back J' hJ', hm]

def Limit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, InScope .csd l π (quadChar E ^ a) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), SplitAtt π ι r ∧
      ∀ w, IsSplitAt w → Apart w w₀ →
        ClauseAt .ss π ι r w ∧ ClauseAt .crys π ι r w ∧ (IwaAt π w → ClauseAt .dR π ι r w)

theorem not_apart_self (w : HeightOneSpectrum (𝓞 E)) : ¬ Apart w w := fun h => h rfl

end GlobalTheory.Cong

end
