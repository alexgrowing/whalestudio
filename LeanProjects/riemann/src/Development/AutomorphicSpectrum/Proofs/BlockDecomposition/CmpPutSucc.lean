import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open GlobalTheory.CatH (face toLast)
universe w w' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.ReesDown

section
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {F : D ⥤ ModuleCat.{w} R} (Ψ : Flt F)

def ev (r : ℕ) (T : D) : Ψ.Pr T →+ F.obj T where
  toFun x := (x r).1
  map_zero' := rfl
  map_add' _ _ := rfl

def cmp (r j : ℕ) (f : Cn Ψ.rees j) : Cn F j := fun s => ev Ψ r _ (f s)

def cmpS (r j : ℕ) (f : Cn Ψ.rees j) : Cn (Ψ.S r).fn j := fun s => (show Ψ.Pr _ from f s) r

def put (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : Cn Ψ.rees j := fun s =>
  show Ψ.Pr _ from fun r => match r with
    | 0 => ⟨z s, by rw [h0]; trivial⟩
    | _ + 1 => 0

theorem cmp_d (r j : ℕ) (f : Cn Ψ.rees j) : cmp Ψ r (j + 1) (d Ψ.rees j f) = d F j (cmp Ψ r j f) := by
  funext s
  refine (map_sum (ev Ψ r _) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_zsmul]
  rfl

theorem cmp_zero (r j : ℕ) : cmp Ψ r j 0 = 0 := rfl

theorem cmp_sub (r j : ℕ) (f g : Cn Ψ.rees j) : cmp Ψ r j (f - g) = cmp Ψ r j f - cmp Ψ r j g := rfl

theorem cmp_put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) : cmp Ψ 0 j (put Ψ h0 j z) = z := rfl

theorem cmp_put_succ (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (r j : ℕ) (z : Cn F j) : cmp Ψ (r + 1) j (put Ψ h0 j z) = 0 := rfl

theorem cochain_ext {j : ℕ} {f g : Cn Ψ.rees j} (h : ∀ r, cmp Ψ r j f = cmp Ψ r j g) : f = g := by
  funext s
  refine funext fun r => Subtype.ext ?_
  exact congrFun (h r) s

theorem put_d (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    d Ψ.rees j (put Ψ h0 j z) = put Ψ h0 (j + 1) (d F j z) := by
  refine cochain_ext Ψ fun r => ?_
  rw [cmp_d]
  cases r with
  | zero => rfl
  | succ r =>
    rw [cmp_put_succ, cmp_put_succ, map_zero]

theorem put_zero (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) : put Ψ h0 j 0 = 0 := by
  refine cochain_ext Ψ fun r => ?_
  cases r <;> rfl

theorem cmp_X (j r : ℕ) (f : Cn Ψ.rees j) : cmp Ψ (r + 1) j ((X : ℤ[X]) • f) = Ψ.μ • cmp Ψ r j f := by
  funext s
  exact Ψ.X_smul_succ _ (f s) r

theorem cmp_X_pow (j k : ℕ) (f : Cn Ψ.rees j) : cmp Ψ k j ((X : ℤ[X]) ^ k • f) = Ψ.μ ^ k • cmp Ψ 0 j f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, cmp_X, ih, pow_succ', mul_smul]

theorem cmp_mem_B (r j : ℕ) (a : Cn Ψ.rees j) (h : a ∈ (cx Ψ.rees).B j) : cmp Ψ r j a ∈ (cx F).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨cmp Ψ r j e, (cmp_d Ψ r j e).symm⟩

theorem put_mem_B (h0 : ∀ T, (Ψ.S 0).S T = ⊤) (j : ℕ) (a : Cn F j) (h : a ∈ (cx F).B j) :
    put Ψ h0 j a ∈ (cx Ψ.rees).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this, put_zero]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨put Ψ h0 j e, put_d Ψ h0 j e⟩

theorem d_cmpS (r j : ℕ) (f : Cn Ψ.rees j) (hf : d Ψ.rees j f = 0) : d (Ψ.S r).fn j (cmpS Ψ r j f) = 0 := by
  funext s
  refine Subtype.ext ?_
  have h1 := congrFun ((Ψ.S r).inc.d_pullC j (cmpS Ψ r j f)) s
  have h2 : d F j (cmp Ψ r j f) = 0 := by rw [← cmp_d, hf, cmp_zero]
  exact h1.symm.trans (congrFun h2 s)

end

end GlobalTheory.CompanionTheory.ReesDown

namespace GlobalTheory.CompanionTheory.ReesDown

theorem put_pull {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (h0 : ∀ T, (Φ.S 0).S T = ⊤) (j : ℕ) (z : Cn F j) :
    (Mor.restrict Φ.rees G).pullC j (put Φ h0 j z) =
      put (Φ.comap G) (fun T => h0 (G.obj T)) j ((Mor.restrict F G).pullC j z) := by
  refine cochain_ext (Φ.comap G) fun r => ?_
  cases r <;> rfl

theorem main : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} (Φ : Flt F) (G : C' ⥤ C) (n N : ℕ), (∀ T, (Φ.S 0).S T = ⊤) → RI ((X : ℤ[X]) ^ N) n Φ.rees G → ∀ j ≤ n, InjUpTo (Φ.μ ^ N) ((Mor.restrict F G).pull j) ∧ ∀ y, ∃ x ∈ (Φ.S N).img j, (Mor.restrict F G).pull j x = Φ.μ ^ N • y := by
  intro R _ C _ C' _ F Φ G n N h0 hRI j hj
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  have h0' : ∀ T, ((Φ.comap G).S 0).S T = ⊤ := fun T => h0 (G.obj T)
  have hpd : ∀ (z : Cn F j), d F j z = 0 → d (G ⋙ F) j ((Mor.restrict F G).pullC j z) = 0 := fun z hz => by
    rw [Mor.d_pullC, hz, map_zero]
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := (P.cls_surj (cx F) j).1 x
    have h2 : (Mor.restrict F G).pullC j z ∈ (cx (G ⋙ F)).B j := by
      have h1 := P.mapH_cls (Mor.restrict F G).hom j z hz (hpd z hz)
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.1 _ _).1 (h1.symm.trans hx)
    have hZ : d Φ.rees j (put Φ h0 j z) = 0 := by
      rw [put_d, hz]; exact put_zero Φ h0 _
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j (put Φ h0 j z)) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have h3 : (Mor.restrict Φ.rees G).pull j ((cx Φ.rees).cls _ hZ) = 0 := by
      refine (P.mapH_cls (Mor.restrict Φ.rees G).hom j _ hZ hZ').trans ?_
      refine ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.1 _ _).2 ?_
      have key : ∀ a : (cx (G ⋙ Φ.rees)).X j, a = put (Φ.comap G) h0' j ((Mor.restrict F G).pullC j z) →
          a ∈ (cx (G ⋙ Φ.rees)).B j := by
        intro a ha
        subst ha
        exact put_mem_B (Φ.comap G) h0' j _ h2
      exact key _ (put_pull Φ G h0 j z)
    have hXZ : d Φ.rees j ((X : ℤ[X]) ^ N • put Φ h0 j z) = 0 := by
      rw [map_smul, hZ, smul_zero]
    have h4 := hU.1 _ h3
    rw [← (P.cls_surj (cx Φ.rees) j).2.2.2.2 _ _ hZ hXZ] at h4
    have h5 := cmp_mem_B Φ N j _ (((P.cls_surj (cx Φ.rees) j).2.1 _ hXZ).1 h4)
    rw [cmp_X_pow, cmp_put_zero] at h5
    have hμ : d F j (Φ.μ ^ N • z) = 0 := by rw [map_smul, hz, smul_zero]
    rw [← (P.cls_surj (cx F) j).2.2.2.2 _ _ hz hμ]
    exact ((P.cls_surj (cx F) j).2.1 _ hμ).2 h5
  · obtain ⟨w, hw, rfl⟩ := (P.cls_surj (cx (G ⋙ F)) j).1 y
    have hW : d (G ⋙ Φ.rees) j (put (Φ.comap G) h0' j w) = 0 := by
      refine (put_d (Φ.comap G) h0' j w).trans ?_
      rw [hw]; exact put_zero (Φ.comap G) h0' _
    obtain ⟨x', hx'⟩ := hU.2 ((cx (G ⋙ Φ.rees)).cls (show (cx (G ⋙ Φ.rees)).X j from put (Φ.comap G) h0' j w) hW)
    obtain ⟨Z, hZ, rfl⟩ := (P.cls_surj (cx Φ.rees) j).1 x'
    have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j Z) = 0 := by
      rw [Mor.d_pullC, hZ, map_zero]
    have hXW : d (G ⋙ Φ.rees) j ((X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) = 0 := by
      rw [map_smul, hW, smul_zero]
    have hx2 := (P.mapH_cls (Mor.restrict Φ.rees G).hom j Z hZ hZ').symm.trans hx'
    rw [← (P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.2.2 _ _ hW hXW] at hx2
    have hB := ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.1 _ _ hZ' hXW).1 hx2
    have hc : (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w ∈ (cx (G ⋙ F)).B j := by
      have h := cmp_mem_B (Φ.comap G) N j _ hB
      have e : ∀ A : Cn (Φ.comap G).rees j, A = (Mor.restrict Φ.rees G).pullC j Z →
          cmp (Φ.comap G) N j (A - (X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) =
            (Mor.restrict F G).pullC j (cmp Φ N j Z) - Φ.μ ^ N • w := by
        intro A hA
        rw [cmp_sub, cmp_X_pow, cmp_put_zero, hA]
        rfl
      exact (e _ rfl) ▸ h
    have hz0 : d F j (cmp Φ N j Z) = 0 := by rw [← cmp_d, hZ, cmp_zero]
    have hμ : d (G ⋙ F) j (Φ.μ ^ N • w) = 0 := by rw [map_smul, hw, smul_zero]
    refine ⟨(cx F).cls _ hz0, ⟨(cx (Φ.S N).fn).cls _ (d_cmpS Φ N j Z hZ), ?_⟩, ?_⟩
    · exact P.mapH_cls (Φ.S N).inc.hom j _ _ hz0
    · refine (P.mapH_cls (Mor.restrict F G).hom j _ hz0 (hpd _ hz0)).trans ?_
      rw [← (P.cls_surj (cx (G ⋙ F)) j).2.2.2.2 _ _ hw hμ]
      exact ((P.cls_surj (cx (G ⋙ F)) j).2.2.1 _ _ _ hμ).2 hc

end GlobalTheory.CompanionTheory.ReesDown
