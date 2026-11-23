import Formalism.LocalToGlobal.Columns.TiedCls
import Formalism.LocalToGlobal.Columns.TiedCH
import Formalism.LocalToGlobal.HermitianForms.BothLemmas

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure HCrd {X : Fields} (Pr : Primes X) (n : ℕ) {cls : Type} (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  n' : ℕ
  hn : n' = n
  J : Matrix (Fin n') (Fin n') X.E
  hJ : J = 1
  f : ℕ
  hf : f = X.f
  bad : Set (HeightOneSpectrum (𝓞 X.F))
  hbad : bad = plUnder X.F Pr.vGs
  lat : cls → Submodule (𝓞 X.E) (Fin n' → X.E)
  hlat : ∀ c, lat c = Formalism.L2.Forms.reL hn.symm (L c)

structure LevPack {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (gp : Fin 2 → ℕ) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  lev : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad
  cls : RecCls hc J lev.Lb lev.U stab lat
  bad_iff : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ bad ↔ ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal)
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F),
    (x ∈ levelVL hc.sig J v lev.Lb ∧ ∀ y ∈ Formalism.L2.Herm.locL v lev.Lb, ∃ z ∈ Formalism.L2.Herm.locL v lev.Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) → x ∈ lev.Uloc v
  UlocAlt : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ lev.Uloc v ↔
    (x ∈ levelVL hc.sig J v lev.Lb ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J lev.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v lev.Lb)

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def LocalLevelIsKOneAtT : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.F), (Pr.T u : 𝓞 X.F) ∈ v.asIdeal → ∀ x : GL (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F),
    x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
    (x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) X.E) v (baseLb X.E n (Pr.vT u)) ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 X.E)
          (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n (Pr.vT u)))),
        (x : Matrix (Fin n) (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (baseLb X.E n (Pr.vT u)))

include hc hPr in

theorem th_plUnder_vGs (v : HeightOneSpectrum (𝓞 X.F)) :
    v ∈ plUnder X.F Pr.vGs ↔ ((Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal ∨ (Pr.g 1 : 𝓞 X.F) ∈ v.asIdeal) := by
  classical
  have key : ∀ (i : Fin 2), v ∈ plUnder X.F (Pr.vG i) ↔ (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
    intro i
    have h0 : X.conjO (Pr.piG i) ≠ 0 := by
      intro h
      have h1 := hPr.piG_norm i
      rw [h, mul_zero] at h1
      exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
    refine mem_plUnder_iff_norm hc (fun P => mem_divs h0 P) (Pr.g i) ?_ v
    have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
    rw [h2, mul_comm]
    exact hPr.piG_norm i
  rw [← key 0, ← key 1]
  constructor
  · rintro ⟨P, hP, h⟩
    rcases Finset.mem_union.1 hP with h' | h'
    · exact Or.inl ⟨P, h', h⟩
    · exact Or.inr ⟨P, h', h⟩
  · rintro (⟨P, hP, h⟩ | ⟨P, hP, h⟩)
    · exact ⟨P, Finset.mem_union_left _ hP, h⟩
    · exact ⟨P, Finset.mem_union_right _ hP, h⟩

variable (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

def levPack₁ (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) :
    LevPack hc n (1 : Matrix (Fin n) (Fin n) X.E) Pr.g (Pr.T u) X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.L) where
  lev := tieLev hc hX hPr σ₀ u Λ
  cls := recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs
  bad_iff := th_plUnder_vGs hc hPr
  Uloc_g := fun i v hv x hx => by
    refine levLoc_of_princ hc n (Pr.vT u) Pr.vGs Λ.grp v (Pr.g i) ?_ ?_ x hx.1 hx.2
    · intro hT
      have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal :=
        (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT
      exact rls_T_notUnder hPr u v h1 ((th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl hv; exact Or.inr hv))
    · intro w _ hov
      have : (Pr.g i : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ hv
      rwa [Ideal.mem_comap, map_natCast] at this
  UlocAlt := hK

def levPack (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) :
    LevPack hc H.n' H.J Pr.g (Pr.T u) H.f H.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) H.lat := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact levPack₁ hc hX hPr σ₀ u Λ c₀ s hS hs hK

end Gen

section Repack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
  {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {cls : Type} {stab : cls → Type}
  [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}

def LevPack.toStep (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.StepLevel hc S gp T f where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := fun x hx => Submodule.subset_span (P.lev.Lb_int x hx)
  Lb_dual := fun y hy => by
    refine Submodule.span_induction (p := fun y _ => (T : E) • y ∈ P.lev.Lb) (fun y hy => P.lev.Lb_dual y hy) ?_ ?_ ?_ hy
    · rw [smul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  Uloc_g := P.Uloc_g
  UlocAlt := P.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq

def LevPack.toCls (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.ClassTie hc S P.toStep.Lb P.toStep.U stab lat where
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := fun c γ => P.cls.stabI_range c γ.1 γ.2

end Repack

end Formalism.L2.Col
