import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TateIsoExistsAlgClosedStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.RationalTorsion

theorem section_ext {K k : Type} [Field K] [Field k] (t : Sp k ⟶ Sp K) {G : Over (Sp K)}
    {s s' : 𝟙_ (Over (Sp K)) ⟶ G} (h : toUnit (Over.mk t) ≫ s = toUnit (Over.mk t) ≫ s') : s = s' := by
  have h1 : Surjective t := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have h2 : Flat t := inferInstance
  have h3 : Epi t := Flat.epi_of_flat_of_surjective t
  have h4 : (toUnit (Over.mk t)).left = t := by simp
  have h5 : Epi (toUnit (Over.mk t)).left := by rw [h4]; exact h3
  have h6 : Epi (toUnit (Over.mk t)) := Over.epi_of_epi_left _
  exact (cancel_epi _).1 h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_add_smul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a c : D.La) :
    I.ev n (a + n • c) = I.ev n a := by
  rw [I.add, (I.ker n hn _).2 ⟨c, rfl⟩, _root_.mul_one]

theorem exists_eq_nsmul (D : Datum H) (l : Level H) {J J' : Ideal (𝓞 E)}
    (hJ : J * J' = Ideal.span {(l.M : 𝓞 E)}) {e : 𝓞 E} (he : e ∈ J) {a : D.La}
    (ha : a ∈ J' • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c, e • a = l.M • c := by
  have h1 : e • a ∈ (J * J') • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he ha
  rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨c, -, hc⟩ := h1
  exact ⟨c, by rw [← hc, Nat.cast_smul_eq_nsmul]⟩

theorem exists_obj : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (K : Type) [Field K] [NumberField K] (j : B →+* K) (σ : K →+* ℂ) (T : PAT H (Sp K)) (I : TateIso D ℂ (Over.mk (spMap σ) ⟶ T.t.G) (fun a x => x ≫ T.t.act.act a) (fun n x x' c => Out.WeilIs T.t.G T.t.PP.L n x x' (unitOn c))), HasType H T.t.act (j b.ρ) D.p D.q → (I.ζ l.A : ℂ) = σ (j b.ζ) → (∀ x : Over.mk (spMap σ) ⟶ T.t.G, x ^ l.M' = 1 → ∃ s : 𝟙_ (Over (Sp K)) ⟶ T.t.G, toUnit _ ≫ s = x) → ∃ o : Obj D l b (spMap j), o.t = T.t := by
  intro laws E _ _ _ H D l B _ b K _ _ j σ T I hty hζ hrat
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hA : 0 < l.A := l.A_pos
  have hsec : ∀ n : ℕ, 0 < n → n ∣ l.M' → ∀ a, ∃ s : 𝟙_ (Over (Sp K)) ⟶ T.t.G, toUnit _ ≫ s = I.ev n a := by
    rintro n hn ⟨m, hm⟩ a
    apply hrat
    rw [hm, pow_mul, (I.onto n hn _).2 ⟨a, rfl⟩, one_pow]
  choose sA hsA using hsec l.A hA (Nat.dvd_lcm_right _ _)
  choose sM hsM using hsec l.M hM (Nat.dvd_lcm_left _ _)
  obtain ⟨f, hf, e, he, hfe⟩ : ∃ f ∈ l.Mb, ∃ e ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E), f + e = 1 :=
    Submodule.mem_sup.1 (by rw [l.coprime]; trivial)
  refine ⟨{
    t := T.t
    proper := T.ab.proper
    ample := T.ample
    ktriv := T.ktriv
    eta := fun a => sM (e • a)
    eta_add := fun a c => section_ext (spMap σ) (by
      rw [MonObj.comp_mul, hsM, hsM, hsM, smul_add, I.add])
    eta_ker := fun a ha => section_ext (spMap σ) (by
      obtain ⟨c, hc⟩ := exists_eq_nsmul D l (by rw [mul_comm]; exact l.prod) he ha
      rw [MonObj.comp_one, hsM]
      exact (I.ker _ hM _).2 ⟨c, hc⟩)
    etaA := sA
    etaA_add := fun a c => section_ext (spMap σ) (by
      rw [MonObj.comp_mul, hsA, hsA, hsA, I.add])
    etaA_ker := fun a => section_ext (spMap σ) (by
      rw [MonObj.comp_one, hsA]
      exact (I.ker _ hA _).2 ⟨a, rfl⟩)
    geom := ?_ }, rfl⟩
  intro k _ _ x β hx
  obtain ⟨ν, rfl⟩ : ∃ ν : K →+* k, x = spMap ν := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  have hβ : β = ν.comp j := by
    have h1 : spMap (ν.comp j) = spMap β := by
      rw [← hx, ← Spec.map_comp]; rfl
    have h2 := Spec.map_injective h1
    exact (congrArg CommRingCat.Hom.hom h2).symm
  subst hβ
  refine ⟨hty k ν ν.injective, ?_⟩
  obtain ⟨I', hζ', hev⟩ := GlobalTheory.T.tate_iso_exists_alg_closed laws E H D K σ T I k ν
  refine ⟨I', hζ' _ _ hA hζ, fun a => hev _ a _ hA (hsA a), fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_nsmul D l l.prod hf ha
  have h1 : a = e • a + l.M • c := by rw [← hc, ← add_smul, add_comm, hfe, one_smul]
  rw [hev _ (e • a) _ hM (hsM _)]
  conv_rhs => rw [h1]
  exact (ev_add_smul I' hM _ _).symm

end GlobalTheory.CM.RationalTorsion
end
