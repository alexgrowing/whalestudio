import Development.EtaleCohomology.EtaleSheaves.LeafKumCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.H2CurveOrder.LeafKumSeqPf

def powNat (q : ℕ) : unitsF ⟶ unitsF where
  app A := ModuleCat.ofHom
    { toFun := fun g => ⟨q • g.down⟩
      map_add' := fun x y => congrArg ULift.up (smul_add q x.down y.down)
      map_smul' := fun c x => congrArg ULift.up (smul_comm q c.down x.down) }
  naturality A B f := by
    ext x
    exact congrArg ULift.up (map_nsmul _ q x.down).symm

def powGm (q : ℕ) : Gm ⟶ Gm := (presheafToSheaf _ _).map (Functor.whiskerLeft Scheme.Γ (powNat q))

def kumSC (q : ℕ) : ShortComplex (Shv ℤ) :=
  ShortComplex.mk (kernel.ι (powGm q)) (cokernel.π (kernel.ι (powGm q))) (cokernel.condition _)

theorem kumSC_shortExact (q : ℕ) : (kumSC q).ShortExact := by
  have hex : (kumSC q).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (kernel.ι (powGm q)))
  exact { exact := hex, mono_f := by dsimp [kumSC]; infer_instance, epi_g := by dsimp [kumSC]; infer_instance }

def LeafKumMu : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  Nonempty (H ℤ (sp B) (kernel (powGm q)) 1 ≃+ Ht q (sp B) 1 1)

def KummerUnitsSurjectH0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  ∃ c : Additive Bˣ →+ H ℤ (sp B) (kumSC q).X₃ 0, Function.Surjective c ∧
    ∀ u : Additive Bˣ, c (q • u) ∈ (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).g 0).range

theorem LeafKumSeq_of (hM : LeafKumMu) (hH : KummerUnitsSurjectH0) : LateralTheory.E.LeafKumCut.LeafKumSeq := by
  intro hy q _ B _ hq
  have hA7 : A7 := hy.2.2.2.2.2.1
  obtain ⟨z, hz⟩ := hA7 ℤ (kumSC q) (kumSC_shortExact q)
  obtain ⟨h1, h2, h3⟩ := hz ((chains ℤ).obj (sp B)) 0
  obtain ⟨e1⟩ := hM hy q B hq
  obtain ⟨c, hcs, hcq⟩ := hH hy q B hq
  let δ : H ℤ (sp B) (kumSC q).X₃ 0 →+ H ℤ (sp B) (kernel (powGm q)) 1 :=
    HK.ext ℤ ((chains ℤ).obj (sp B)) z 0 (0 + 1) rfl
  have h2 : Function.Exact (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).g 0) δ := h2
  have h3 : Function.Exact δ (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).f 1) := h3
  let g : Additive Bˣ →+ Ht q (sp B) 1 1 := e1.toAddMonoidHom.comp (δ.comp c)
  let φ : Bˣ →* Multiplicative (Ht q (sp B) 1 1) :=
    { toFun := fun u => Multiplicative.ofAdd (g (Additive.ofMul u))
      map_one' := by simp
      map_mul' := fun x y => by simp only [ofMul_mul, map_add, ofAdd_add] }
  have hφ : (powMonoidHom q : Bˣ →* Bˣ).range ≤ φ.ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    have hz0 : δ (c (q • Additive.ofMul u)) = 0 := (h2 _).mpr (hcq _)
    show Multiplicative.ofAdd (e1 (δ (c (Additive.ofMul (u ^ q))))) = 1
    rw [ofMul_pow, hz0, map_zero]
    rfl
  let ψ := QuotientGroup.lift _ φ hφ
  let a : Additive (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) →+ Ht q (sp B) 1 1 :=
    { toFun := fun x => Multiplicative.toAdd (ψ (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun x y => by simp only [toMul_add, map_mul, toAdd_mul] }
  refine ⟨a,
    (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).f 1).comp e1.symm.toAddMonoidHom, ?_⟩
  intro y
  constructor
  · intro hb
    obtain ⟨w, hw⟩ := (h3 (e1.symm y)).mp hb
    obtain ⟨v, rfl⟩ := hcs w
    refine ⟨Additive.ofMul (QuotientGroup.mk (Additive.toMul v)), ?_⟩
    show e1 (δ (c (Additive.ofMul (Additive.toMul v)))) = y
    rw [ofMul_toMul]
    rw [hw]; simp
  · rintro ⟨x, rfl⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hx : x = Additive.ofMul (QuotientGroup.mk u) := by rw [hu]; rfl
    subst hx
    show HK.post ℤ _ (kumSC q).f 1 (e1.symm (e1 (δ (c (Additive.ofMul u))))) = 0
    rw [AddEquiv.symm_apply_apply]
    exact (h3 _).mpr ⟨_, rfl⟩

end LateralTheory.E.H2CurveOrder.LeafKumSeqPf
