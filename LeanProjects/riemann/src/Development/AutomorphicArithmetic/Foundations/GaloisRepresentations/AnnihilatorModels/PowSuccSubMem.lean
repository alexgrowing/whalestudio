import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdemKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem idem_mod {A : Type} [CommRing A] {P α β : A} {J : Ideal A}
    (h1 : β * α ∈ Ideal.span {P}) (h2 : α + β - 1 ∈ Ideal.span {P}) (hJ : Ideal.span {P} ≤ J) :
    β * β - β ∈ J := by
  have : β * β - β = β * (α + β - 1) - β * α := by ring
  rw [this]
  exact J.sub_mem (J.mul_mem_left _ (hJ h2)) (hJ h1)

private theorem pow_succ_sub_mem {A : Type} [CommRing A] {β : A} {J : Ideal A} (h : β * β - β ∈ J) (k : ℕ) :
    β ^ (k + 1) - β ∈ J := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : β ^ (k + 1 + 1) - β = β * (β ^ (k + 1) - β) + (β * β - β) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left _ ih) h

private theorem mem_of_pow_le {A : Type} [CommRing A] {P α β : A} {u J : Ideal A} {n k : ℕ} (hn : n ≠ 0)
    (h1 : β * α ∈ Ideal.span {P}) (h2 : α + β - 1 ∈ Ideal.span {P}) (h3 : β ∈ u ^ n)
    (hJ : Ideal.span {P} ≤ J) (hk : u ^ k ≤ J) : β ∈ J := by
  have hp := pow_succ_sub_mem (idem_mod h1 h2 hJ) k
  have hm : β ^ (k + 1) ∈ u ^ k := by
    have h4 : β ^ (k + 1) ∈ (u ^ n) ^ (k + 1) := Ideal.pow_mem_pow h3 _
    rw [← pow_mul] at h4
    refine Ideal.pow_le_pow_right ?_ h4
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn
    nlinarith
  have : β = β ^ (k + 1) - (β ^ (k + 1) - β) := by ring
  rw [this]
  exact J.sub_mem (hk hm) hp

private theorem pow_le_of_mem {A : Type} [CommRing A] {P α β : A} {u J : Ideal A} {n : ℕ}
    (h1 : ∀ a ∈ u ^ n, a * α ∈ Ideal.span {P}) (h2 : α + β - 1 ∈ Ideal.span {P})
    (hJ : Ideal.span {P} ≤ J) (hβ : β ∈ J) : u ^ n ≤ J := fun x hx => by
  have : x = x * α - x * (α + β - 1) + x * β := by ring
  rw [this]
  exact J.add_mem (J.sub_mem (hJ (h1 x hx)) (J.mul_mem_left _ (hJ h2))) (J.mul_mem_left _ hβ)

theorem UpperTheory.Gal.crystallineComparison.Mod.kerU_of :
    UElt → KerU := by
  intro hU p _ D R _ b N r w hw hu S _ s o o' ψ ψ' e hm hm' hlin h1 h2
  obtain ⟨α, hα1, hα2, hα3⟩ := hU p D r w hw hu e
  have hc0 : p ^ e ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  obtain ⟨hfin, hflat⟩ := GlobalTheory.T.isFinite_flat_abelianSchemeHom_of_quasiInverse S o.A o'.A o.ab o'.ab ψ ψ' (p ^ e) hc0 hm hm' h1 h2
  let ρ : 𝓞 D.F → (o.A ⟶ o.A) := fun a => o.act.act (algebraMap (𝓞 D.F) D.O a)
  have ρhom : ∀ a, IsMonHom (ρ a) := fun a => o.act.hom _
  have ρmul : ∀ a a', ρ (a * a') = ρ a ≫ ρ a' := fun a a' => by
    simp only [ρ]; rw [mul_comm, map_mul, o.act.mul]
  have ρadd : ∀ a a', ρ (a + a') = ρ a * ρ a' := fun a a' => by
    simp only [ρ]; rw [map_add, o.act.add]
  have ρ0 : ρ 0 = 1 := by
    have := ρadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have ρc : ρ ((p : 𝓞 D.F) ^ e) = 𝟙 o.A ^ (p ^ e) := by
    have : ((p : 𝓞 D.F) ^ e) = ((p ^ e : ℕ) : 𝓞 D.F) := by push_cast; rfl
    simp only [ρ]
    rw [this, map_natCast, GlobalTheory.IwLevel.HTTorsionFF.oActN_natCast]

  let I : ∀ {T : Over S}, (T ⟶ o.A) → Ideal (𝓞 D.F) := fun {T} z =>
    { carrier := {a | z ≫ ρ a = 1}
      add_mem' := fun {a a'} ha ha' => by
        haveI := ρhom a
        show z ≫ ρ (a + a') = 1
        rw [ρadd, MonObj.comp_mul, show z ≫ ρ a = 1 from ha, show z ≫ ρ a' = 1 from ha', _root_.mul_one]
      zero_mem' := by
        show z ≫ ρ 0 = 1
        rw [ρ0, MonObj.comp_one]
      smul_mem' := fun c a ha => by
        haveI := ρhom c
        show z ≫ ρ (c * a) = 1
        rw [mul_comm, ρmul, ← Category.assoc, show z ≫ ρ a = 1 from ha, MonObj.one_comp] }
  have memI : ∀ {T : Over S} (z : T ⟶ o.A) (a), a ∈ I z ↔ z ≫ ρ a = 1 := fun _ _ => Iff.rfl
  have kerP : ∀ {T : Over S} (z : T ⟶ o.A), z ≫ ψ = 1 → z ^ p ^ e = 1 := fun {T} z hz => by
    have : z ≫ ψ ≫ ψ' = 1 := by rw [← Category.assoc, hz, MonObj.one_comp]
    rwa [h1, MonObj.comp_pow, Category.comp_id] at this
  have spanI : ∀ {T : Over S} (z : T ⟶ o.A), z ≫ ψ = 1 → Ideal.span {(p : 𝓞 D.F) ^ e} ≤ I z := fun z hz => by
    rw [Ideal.span_singleton_le_iff_mem, memI, ρc, MonObj.comp_pow, Category.comp_id]
    exact kerP z hz
  have cong : ∀ {T : Over S} (z : T ⟶ o.A) (a a'), a - a' ∈ I z → z ≫ ρ a = z ≫ ρ a' := fun z a a' h => by
    haveI := ρhom a'
    haveI := ρhom (a - a')
    have : a = a' + (a - a') := by ring
    rw [this, ρadd, MonObj.comp_mul, show z ≫ ρ (a - a') = 1 from h, _root_.mul_one]
  set β := D.bar α with hβ
  have hβα : β * α ∈ Ideal.span {(p : 𝓞 D.F) ^ e} := hα1 β hα3
  obtain ⟨K, gK, i, -, hmono, hKfin, hKflat, hK⟩ := GlobalTheory.UPel.HT.ES.OrdCount.exists_idem_kernel S o.A o'.A ψ (ρ β) hm (ρhom β)
    hfin hflat (fun T z hz => ⟨by
      haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O β)
      rw [Category.assoc, hlin, ← Category.assoc, hz, MonObj.one_comp], by
      rw [Category.assoc, ← ρmul]
      exact cong z _ _ (idem_mod hβα hα2 (spanI z hz))⟩)
  have key : ∀ (T : Over S) (g : T ⟶ o.A), (g ≫ ψ = 1 ∧ g ≫ ρ β = 1) ↔ UKer r o ψ T g := fun T g => by
    refine ⟨fun ⟨ha, hb⟩ => ⟨ha, e, fun a haI => pow_le_of_mem hα1 hα2 (spanI g ha) hb haI⟩, fun ⟨ha, k, hk⟩ => ⟨ha, ?_⟩⟩
    rcases Nat.eq_zero_or_pos e with rfl | he
    · have : (1 : 𝓞 D.F) ∈ I g := spanI g ha (by simp)
      exact Ideal.mem_of_one_mem this β
    · exact mem_of_pow_le he.ne' hβα hα2 hα3 (spanI g ha) (fun a haI => hk a haI)
  refine ⟨⟨K, i, hmono, hKfin, hKflat, fun T g => (hK T g).trans (key T g)⟩, fun T => ⟨?_, fun g h hg hh => ?_⟩,
    fun T g hg => kerP g hg.1⟩
  · exact (key T 1).1 ⟨by rw [MonObj.one_comp], by haveI := ρhom β; rw [MonObj.one_comp]⟩
  · obtain ⟨g1, g2⟩ := (key T g).2 hg
    obtain ⟨h1', h2'⟩ := (key T h).2 hh
    haveI := ρhom β
    refine (key T _).1 ⟨?_, ?_⟩
    · rw [← div_eq_mul_inv, GrpObj.div_comp, g1, h1', div_one]
    · rw [← div_eq_mul_inv, GrpObj.div_comp, g2, h2', div_one]
